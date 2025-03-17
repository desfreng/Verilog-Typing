{-# LANGUAGE OverloadedStrings #-}

module Context where

import Ast
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable
import Data.Functor
import Data.GraphViz (X11Color (Black, White), textLabel)
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
    exprContexts :: Map AstId Int,
    exprBaseSize :: Map AstId Size,
    ctxDependencies :: IntMap Int
  }

setExprContext :: Int -> Expr -> State GCInfo ()
setExprContext ctx e = modify $ \s -> s {exprContexts = Map.insert (idFromExpr e) ctx (exprContexts s)}

updateContextSize :: AstId -> Int -> Size -> State GCInfo ()
updateContextSize eId ctxId size = modify $ \s ->
  s
    { contextVals = IntMap.insertWith max ctxId size (contextVals s),
      exprBaseSize = Map.insert eId size (exprBaseSize s)
    }

contextSize :: Int -> State GCInfo Size
contextSize cxtId = gets $ \s -> (IntMap.!) (contextVals s) cxtId

exprInFreshContext :: Maybe Size -> Maybe Int -> Expr -> State GCInfo Int
exprInFreshContext defS dep e = do
  newCtx <- state $ \s ->
    ( nextContext s,
      s
        { nextContext = nextContext s + 1,
          contextVals = maybe (contextVals s) (\def -> IntMap.insert (nextContext s) def (contextVals s)) defS
        }
    )
  () <- modify $ addDependency newCtx dep
  () <- ctxDetermined e newCtx
  return newCtx
  where
    addDependency _ Nothing s = s
    addDependency newId (Just parentId) s = s {ctxDependencies = IntMap.insert newId parentId (ctxDependencies s)}

selfDetermined :: Maybe Int -> Expr -> State GCInfo ()
selfDetermined dep = ($> ()) . exprInFreshContext Nothing dep

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
      selfDetermined Nothing arg
      updateContextSize eId curCtx sizeOne
    childrenContext (Cast _ arg) = do
      argCtx <- exprInFreshContext Nothing (Just curCtx) arg
      argSize <- contextSize argCtx
      updateContextSize eId curCtx argSize
    childrenContext (Comparison _ lhs rhs) = do
      argCtx <- exprInFreshContext Nothing Nothing lhs
      ctxDetermined rhs argCtx
      updateContextSize eId curCtx sizeOne
    childrenContext (Logic _ lhs rhs) = do
      selfDetermined Nothing lhs
      selfDetermined Nothing rhs
      updateContextSize eId curCtx sizeOne
    childrenContext (Reduction _ arg) = do
      selfDetermined Nothing arg
      updateContextSize eId curCtx sizeOne
    childrenContext (Shift _ lhs rhs) = do
      ctxDetermined lhs curCtx
      selfDetermined Nothing rhs
    childrenContext (Pow lhs rhs) = do
      ctxDetermined lhs curCtx
      selfDetermined Nothing rhs
    childrenContext (BinOpAssign lhs _ expr) = do
      _ <- exprInFreshContext (Just $ leftSize lhs) Nothing expr
      updateContextSize eId curCtx (leftSize lhs)
    childrenContext (ShiftAssign lhs _ expr) = do
      selfDetermined Nothing expr
      updateContextSize eId curCtx (leftSize lhs)
    childrenContext (Conditional cond tBranch fBranch) = do
      selfDetermined Nothing cond
      ctxDetermined tBranch curCtx
      ctxDetermined fBranch curCtx
    childrenContext (Concat l) = do
      argsSize <- foldlM (\s arg -> (s +) <$> (exprInFreshContext Nothing (Just curCtx) arg >>= contextSize)) 0 l
      updateContextSize eId curCtx argsSize
    childrenContext (ReplConcat i l) = do
      Ast.Size argsSize <- foldlM (\s arg -> (s +) <$> (exprInFreshContext Nothing (Just curCtx) arg >>= contextSize)) 0 l
      updateContextSize eId curCtx (Ast.Size $ argsSize * i)
    childrenContext (Inside arg l) = do
      newCxt <- exprInFreshContext Nothing Nothing arg
      mapM_ (flip ctxDetermined newCxt) l

newtype GCReader a = GCReader {runGCReader :: Reader GCInfo a}
  deriving (Functor, Applicative, Monad, MonadReader GCInfo)

instance (Semigroup a) => Semigroup (GCReader a) where
  (<>) :: (Semigroup a) => GCReader a -> GCReader a -> GCReader a
  (<>) = liftA2 (<>)

instance (Monoid a) => Monoid (GCReader a) where
  mempty :: (Monoid a) => GCReader a
  mempty = pure mempty

exprCtx :: AstId -> GCReader Int
exprCtx eId = asks $ \r -> (Map.!) (exprContexts r) eId

ctxSize :: Int -> GCReader Size
ctxSize cxtId = asks $ \s -> (IntMap.!) (contextVals s) cxtId

baseSize :: AstId -> GCReader (Maybe Size)
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

buildDepGraph :: GCReader (Dot Text)
buildDepGraph = do
  deps <- asks ctxDependencies
  maxCtx <- asks nextContext
  nodeList <- foldMap addNode $ [0 .. (maxCtx - 1)]
  let edgesList = IntMap.foldMapWithKey go deps
   in return $ nodeList <> edgesList
  where
    addNode ctxId =
      do
        (bg, text) <- colOfInt ctxId
        let attrs =
              [ FillColor [toWC bg],
                FontColor text,
                Style [SItem Filled []],
                textLabel $ "Context " <> T.show ctxId
              ]
        return $ node (nodeIdent ctxId) attrs
    go child parent = edge (nodeIdent parent) (nodeIdent child) []

    nodeIdent ctxId = "ctx" <> T.show ctxId

instance ExprToGraph GCReader where
  prefix :: GCReader Text
  prefix = return "ast"

  exprText :: Expr -> Text -> GCReader Text
  exprText expr lbl =
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

  exprAttr :: AstId -> GCReader Attributes
  exprAttr eId = do
    ctx <- exprCtx eId
    (bg, text) <- colOfInt ctx
    return [FillColor [toWC bg], FontColor text, Style [SItem Filled []]]

  lValueText :: LeftValue -> Text -> GCReader Text
  lValueText lValue txt = return $ txt <> "\nsize: " <> T.show (leftSize lValue)

  lValueAttr :: AstId -> GCReader Attributes
  lValueAttr _ = return [Style [SItem Dashed []]]

  edgesAttr :: AstId -> AstId -> GCReader Attributes
  edgesAttr _ _ = pure []

  transformGraph :: ExprName -> Expr -> Dot Text -> GCReader (Dot Text)
  transformGraph eName _ g =
    let txt = "Ast of " <> T.show eName
        depTxt = "Dependency Graph of " <> T.show eName
        astG = graphAttrs [Comment $ txt, Label $ StrLabel txt] <> g
     in do
          ctxDepGraph <- buildDepGraph
          let ctxG = graphAttrs [Comment $ depTxt, Label $ StrLabel depTxt] <> ctxDepGraph
          return $ cluster (Str "Ast") astG <> cluster (Str "Dependencies") ctxG

contextToGraphs :: ExprName -> Expr -> DotGraph Text
contextToGraphs eName e =
  let initialGCInfo =
        GCInfo
          { nextContext = 0,
            contextVals = mempty,
            exprContexts = mempty,
            exprBaseSize = mempty,
            ctxDependencies = mempty
          }
      s = execState (exprInFreshContext Nothing Nothing e) initialGCInfo
   in runReader (runGCReader $ buildGraph eName e) s