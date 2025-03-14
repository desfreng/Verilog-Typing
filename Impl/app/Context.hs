{-# LANGUAGE OverloadedStrings #-}

module Context where

import Ast
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable
import Data.Functor
import Data.GraphViz (X11Color (Black, White))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Graph
import Graphics.Color.Model qualified as CM

sizeOne :: Size
sizeOne = (Ast.Size 1)

-- Graph Cutting
data GCInfo = GCInfo
  { nextContext :: Int,
    contextVals :: IntMap Size,
    exprContexts :: Map ExprId Int,
    exprBaseSize :: Map ExprId Size
  }

setExprContext :: Int -> Expr -> State GCInfo ()
setExprContext ctx e = modify $ \s -> s {exprContexts = Map.insert (idFromExpr e) ctx (exprContexts s)}

updateContextSize :: ExprId -> Int -> Size -> State GCInfo ()
updateContextSize eId ctxId size = modify $ \s ->
  s
    { contextVals = IntMap.insertWith max ctxId size (contextVals s),
      exprBaseSize = Map.insert eId size (exprBaseSize s)
    }

contextSize :: Int -> State GCInfo Size
contextSize cxtId = gets $ \s -> (IntMap.!) (contextVals s) cxtId

exprInFreshContext :: Expr -> State GCInfo Int
exprInFreshContext e = do
  newCtx <- state $ \s -> (nextContext s, s {nextContext = nextContext s + 1})
  () <- ctxDetermined e newCtx
  return newCtx

selfDetermined :: Expr -> State GCInfo ()
selfDetermined = ($> ()) . exprInFreshContext

ctxDetermined :: Expr -> Int -> State GCInfo ()
ctxDetermined e curCtx =
  setExprContext curCtx e >> childrenContext (exprKind e)
  where
    eId = idFromExpr e
    childrenContext (Operand (Op {opSize})) = updateContextSize eId curCtx opSize
    childrenContext (IntegerValue (VInteger {size})) = updateContextSize eId curCtx size
    childrenContext (Arithmetic _ lhs rhs) = do
      ctxDetermined lhs curCtx
      ctxDetermined rhs curCtx
    childrenContext (PreUnOp _ arg) = ctxDetermined arg curCtx
    childrenContext (PostUnOp _ arg) = ctxDetermined arg curCtx
    childrenContext (LogicNot arg) = do
      selfDetermined arg
      updateContextSize eId curCtx sizeOne
    childrenContext (Cast _ arg) = do
      argCtx <- exprInFreshContext arg
      argSize <- contextSize argCtx
      updateContextSize eId curCtx argSize
    childrenContext (Comparison _ lhs rhs) = do
      argCtx <- exprInFreshContext lhs
      ctxDetermined rhs argCtx
      updateContextSize eId curCtx sizeOne
    childrenContext (Logic _ lhs rhs) = do
      selfDetermined lhs
      selfDetermined rhs
      updateContextSize eId curCtx sizeOne
    childrenContext (Reduction _ arg) = do
      selfDetermined arg
      updateContextSize eId curCtx sizeOne
    childrenContext (Shift _ lhs rhs) = do
      ctxDetermined lhs curCtx
      selfDetermined rhs
    childrenContext (Pow lhs rhs) = do
      ctxDetermined lhs curCtx
      selfDetermined rhs
    childrenContext (BinOpAssign v _ expr) = do
      varCtx <- exprInFreshContext v
      varSize <- contextSize varCtx
      ctxDetermined expr varCtx
      updateContextSize eId curCtx varSize
    childrenContext (ShiftAssign v _ expr) = do
      varCtx <- exprInFreshContext v
      varSize <- contextSize varCtx
      selfDetermined expr
      updateContextSize eId curCtx varSize
    childrenContext (Conditional cond tBranch fBranch) = do
      selfDetermined cond
      ctxDetermined tBranch curCtx
      ctxDetermined fBranch curCtx
    childrenContext (Concat l) = do
      argsSize <- foldlM (\s arg -> (s +) <$> (exprInFreshContext arg >>= contextSize)) 0 l
      updateContextSize eId curCtx argsSize
    childrenContext (ReplConcat i l) = do
      Ast.Size argsSize <- foldlM (\s arg -> (s +) <$> (exprInFreshContext arg >>= contextSize)) 0 l
      updateContextSize eId curCtx (Ast.Size $ argsSize * i)
    childrenContext (Inside arg l) = do
      newCxt <- exprInFreshContext arg
      mapM_ (flip ctxDetermined newCxt) l

newtype GCReader a = GCReader {runGCReader :: Reader GCInfo a}
  deriving (Functor, Applicative, Monad, MonadReader GCInfo)

exprCtx :: ExprId -> GCReader Int
exprCtx eId = asks $ \r -> (Map.!) (exprContexts r) eId

ctxSize :: Int -> GCReader Size
ctxSize cxtId = asks $ \s -> (IntMap.!) (contextVals s) cxtId

baseSize :: ExprId -> GCReader (Maybe Size)
baseSize eId = asks $ Map.lookup eId . exprBaseSize

bgColor :: Double -> Color
bgColor h =
  let (CM.ColorRGB r g b) = CM.hsv2rgb $ CM.ColorHSV h 1 1
      l = r * 0.299 + g * 0.587 + b * 0.114
   in if l > 0.57 then toColor Black else toColor White

colOfInt :: Int -> GCReader (Color, Color)
colOfInt x = do
  maxCtx <- asks nextContext
  let h = fromIntegral x / fromIntegral maxCtx
   in return (HSV h 1 1, bgColor h)

instance ExprToGraph GCReader where
  tagText :: Expr -> Text -> GCReader Text
  tagText expr lbl =
    let eId = idFromExpr expr
     in do
          ctxS <- exprCtx eId >>= ctxSize
          baseS <- baseSize eId
          return $ case baseS of
            Nothing -> lbl <> "\nsize: " <> T.show ctxS
            Just bS ->
              if bS < ctxS
                then lbl <> "\nsize: " <> T.show bS <> " -> " <> T.show ctxS
                else lbl <> "\nsize: " <> T.show ctxS

  nodeAttr :: ExprId -> GCReader Attributes
  nodeAttr eId = do
    ctx <- exprCtx eId
    (bg, text) <- colOfInt ctx
    return [FillColor [toWC bg], FontColor text, Style [SItem Filled []]]

  edgesAttr :: ExprId -> ExprId -> GCReader Attributes
  edgesAttr _ _ = pure []

  transformGraph :: ExprName -> Expr -> Dot ExprId -> GCReader (Dot ExprId)
  transformGraph eName _ g =
    let txt = "Graph for " <> T.show eName
     in return $ graphAttrs [Comment $ txt, Label $ StrLabel txt] <> g

contextToGraphs :: ExprName -> Expr -> DotGraph ExprId
contextToGraphs eName e =
  let initialGCInfo = GCInfo {nextContext = 0, contextVals = mempty, exprContexts = mempty, exprBaseSize = mempty}
      s = execState (exprInFreshContext e) initialGCInfo
   in runReader (runGCReader $ buildGraph eName e) s