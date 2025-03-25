{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

module Graph
  ( ExprToGraph
      ( exprText,
        exprAttr,
        lValueText,
        lValueAttr,
        edgesAttr,
        transformGraph,
        buildGraph,
        prefix
      ),
    exprToGraph,
    colorNode,
  )
where

import Control.Monad.Identity (Identity (runIdentity))
import Data.GraphViz.Attributes hiding (bgColor)
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.Types.Monadic
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Expr
import Graphics.Color.Model qualified as CM
import Model

numChildren :: (Foldable t) => [(Text, a)] -> t a -> [(Text, a)]
numChildren beg l = snd $ foldl addChild (0, beg) l
  where
    addChild :: (Int, [(Text, a)]) -> a -> (Int, [(Text, a)])
    addChild (argId, acc) e = (argId + 1, ("arg" <> T.show argId, e) : acc)

children :: ExprKind -> [(Text, Either LeftValue Expr)]
children (Operand _) = mempty
children (IntegerValue _) = mempty
children (Arithmetic _ lhs rhs) = [("lhs", Right lhs), ("rhs", Right rhs)]
children (PreUnOp _ arg) = [("arg", Right arg)]
children (PostUnOp _ arg) = [("arg", Right arg)]
children (Cast _ arg) = [("arg", Right arg)]
children (Comparison _ lhs rhs) = [("lhs", Right lhs), ("rhs", Right rhs)]
children (LogicNot arg) = [("arg", Right arg)]
children (Logic _ lhs rhs) = [("lhs", Right lhs), ("rhs", Right rhs)]
children (Reduction _ arg) = [("arg", Right arg)]
children (Shift _ lhs rhs) = [("lhs", Right lhs), ("rhs", Right rhs)]
children (Pow lhs rhs) = [("lhs", Right lhs), ("rhs", Right rhs)]
children (BinOpAssign v _ expr) = [("lvalue", Left v), ("expr", Right expr)]
children (ShiftAssign v _ expr) = [("lvalue", Left v), ("expr", Right expr)]
children (Conditional cond tBranch fBranch) =
  [("cond", Right cond), ("true", Right tBranch), ("false", Right fBranch)]
children (Concat l) = numChildren [] $ Right <$> l
children (ReplConcat _ l) = numChildren [] $ Right <$> l
children (Inside arg l) = numChildren [("item", Right arg)] $ Right <$> l

lValueChildren :: LeftValue -> [(Text, Either LeftValue a)]
lValueChildren (LeftAtom _ _) = mempty
lValueChildren (LeftConcat {args}) = numChildren [] $ Left <$> args

exprLabel :: ExprKind -> Text
exprLabel (Operand e) = T.show e
exprLabel (IntegerValue v) = T.show v
exprLabel (Arithmetic op _ _) = T.show op
exprLabel (PreUnOp op _) = T.show op
exprLabel (PostUnOp op _) = T.show op
exprLabel (Cast sig _) = T.show sig <> " cast"
exprLabel (Comparison op _ _) = T.show op
exprLabel (LogicNot _) = "Unary Not"
exprLabel (Logic op _ _) = T.show op
exprLabel (Reduction op _) = "Reduction " <> T.show op
exprLabel (Shift op _ _) = T.show op
exprLabel (Pow _ _) = "Power"
exprLabel (BinOpAssign _ None _) = "Assignment"
exprLabel (BinOpAssign _ op _) = T.show op <> " Assignment"
exprLabel (ShiftAssign _ op _) = T.show op <> " Assignment"
exprLabel (Conditional _ _ _) = "Conditional"
exprLabel (Concat _) = "Concatenation"
exprLabel (ReplConcat i _) = "Replication (x" <> T.show i <> ")"
exprLabel (Inside _ _) = "Inside"

lValueLabel :: LeftValue -> Text
lValueLabel (LeftAtom op _) = T.show op
lValueLabel (LeftConcat _ _ _) = "Concatenation"

bgColorHSV :: (RealFrac a) => a -> a -> a -> Color
bgColorHSV h s v =
  let (CM.ColorRGB r g b) = CM.hsv2rgb $ CM.ColorHSV h s v
   in bgColorRGB r g b

bgColorRGB :: (RealFrac a) => a -> a -> a -> Color
bgColorRGB r g b =
  let l = r * 0.299 + g * 0.587 + b * 0.114
   in if l > 0.57 then toColor Black else toColor White

bgColor :: Color -> Color
bgColor (RGB r g b) = bgColorRGB (fromIntegral r / 255 :: Double) (fromIntegral g / 255) (fromIntegral b / 255)
bgColor (HSV h s v) = bgColorHSV h s v
bgColor _ = error "Unable to extract color components"

colorNode :: Color -> Attributes
colorNode bgCol = [FillColor [toWC bgCol], FontColor $ bgColor bgCol, Style [SItem Filled []]]

class (Monad m) => ExprToGraph m where
  prefix :: ExprId -> m Text
  exprText :: Expr -> Text -> m Text
  exprAttr :: ExprId -> m Attributes
  lValueText :: LeftValue -> Text -> m Text
  lValueAttr :: ExprId -> m Attributes

  edgesAttr :: ExprId -> ExprId -> m Attributes
  transformGraph :: ExprName -> Expr -> Dot Text -> m (Dot Text)

  addAstEdge :: ExprId -> (Text, Either LeftValue Expr) -> m (Dot Text)
  addAstEdge parentId (edgeName, childExpr) =
    let childId = exprId childExpr
     in do
          pId <- prefix parentId
          cId <- prefix childId
          edgeCustomAttr <- (textLabel edgeName :) <$> edgesAttr parentId childId
          return $ edge pId cId $ edgeCustomAttr
  buildExprGraph :: Either LeftValue Expr -> m (Dot Text)
  buildExprGraph expr =
    let eId = exprId expr
        c = either lValueChildren (children . exprKind) expr
     in do
          nodeId <- prefix eId
          nodeLabel <- either (\l -> lValueText l $ lValueLabel l) (\e -> exprText e . exprLabel $ exprKind e) expr
          nodeCustomAttr <- either (const $ lValueAttr eId) (const $ exprAttr eId) expr
          edgesDef <- mconcat <$> mapM (addAstEdge eId) c
          childDefs <- mconcat <$> mapM (buildExprGraph . snd) c
          return $ node nodeId (textLabel nodeLabel : nodeCustomAttr) <> edgesDef <> childDefs

  buildGraph :: ExprName -> Expr -> m (Dot Text)
  buildGraph eName expr = buildExprGraph (Right expr) >>= transformGraph eName expr

instance ExprToGraph Identity where
  prefix :: ExprId -> Identity Text
  prefix = return . T.show

  exprText :: Expr -> Text -> Identity Text
  exprText expr txt =
    return $ case exprKind expr of
      Operand (Op {opSize}) -> txt <> "\nsize:" <> T.show opSize
      _ -> txt

  exprAttr :: ExprId -> Identity Attributes
  exprAttr _ = pure []

  lValueText :: LeftValue -> Text -> Identity Text
  lValueText lValue txt = return $ txt <> "\nsize: " <> T.show (leftSize lValue)

  lValueAttr :: ExprId -> Identity Attributes
  lValueAttr _ = return [Style [SItem Dashed []]]

  edgesAttr :: ExprId -> ExprId -> Identity Attributes
  edgesAttr _ _ = pure []

  transformGraph :: ExprName -> Expr -> Dot Text -> Identity (Dot Text)
  transformGraph eName _ g =
    let txt = "Ast of " <> T.show eName
     in return $ graphAttrs [Comment txt, textLabel txt] <> g

exprToGraph :: ExprName -> Expr -> Dot Text
exprToGraph eName = runIdentity . buildGraph eName