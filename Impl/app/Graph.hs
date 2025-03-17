{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

module Graph
  ( ExprToGraph (prefix, exprText, exprAttr, lValueText, lValueAttr, edgesAttr, transformGraph, buildGraph),
    exprToGraph,
    module Data.GraphViz.Types.Monadic,
    module Data.GraphViz.Attributes.Complete,
    DotGraph,
  )
where

import Ast
import Control.Monad.Identity (Identity (runIdentity))
import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.Types.Generalised (DotGraph)
import Data.GraphViz.Types.Monadic
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T

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

class (Monad m) => ExprToGraph m where
  exprText :: Expr -> Text -> m Text
  exprAttr :: AstId -> m Attributes
  lValueText :: LeftValue -> Text -> m Text
  lValueAttr :: AstId -> m Attributes
  prefix :: m Text

  edgesAttr :: AstId -> AstId -> m Attributes
  transformGraph :: ExprName -> Expr -> Dot Text -> m (Dot Text)

  addAstEdge :: AstId -> (Text, Either LeftValue Expr) -> m (Dot Text)
  addAstEdge parentId (edgeName, childExpr) =
    let childId = either idFromLValue idFromExpr childExpr
     in do
          p <- prefix
          edgeCustomAttr <- (textLabel edgeName :) <$> edgesAttr parentId childId
          return $ edge (p <> T.show parentId) (p <> T.show childId) $ edgeCustomAttr
  buildExprGraph :: Either LeftValue Expr -> m (Dot Text)
  buildExprGraph expr =
    let astId = either idFromLValue idFromExpr expr
        c = either lValueChildren (children . exprKind) expr
     in do
          p <- prefix
          nodeLabel <- either (\l -> lValueText l $ lValueLabel l) (\e -> exprText e . exprLabel $ exprKind e) expr
          nodeCustomAttr <- either (const $ lValueAttr astId) (const $ exprAttr astId) expr
          edgesDef <- mconcat <$> mapM (addAstEdge astId) c
          childDefs <- mconcat <$> mapM (buildExprGraph . snd) c
          return $ node (p <> T.show astId) (textLabel nodeLabel : nodeCustomAttr) <> edgesDef <> childDefs

  buildGraph :: ExprName -> Expr -> m (DotGraph Text)
  buildGraph eName expr =
    digraph' <$> (buildExprGraph (Right expr) >>= transformGraph eName expr)

instance ExprToGraph Identity where
  prefix :: Identity Text
  prefix = return "node"

  exprText :: Expr -> Text -> Identity Text
  exprText expr txt =
    return $ case exprKind expr of
      Operand (Op {opSize}) -> txt <> "\nsize:" <> T.show opSize
      _ -> txt

  exprAttr :: AstId -> Identity Attributes
  exprAttr _ = pure []

  lValueText :: LeftValue -> Text -> Identity Text
  lValueText lValue txt = return $ txt <> "\nsize: " <> T.show (leftSize lValue)

  lValueAttr :: AstId -> Identity Attributes
  lValueAttr _ = return [Style [SItem Dashed []]]

  edgesAttr :: AstId -> AstId -> Identity Attributes
  edgesAttr _ _ = pure []

  transformGraph :: ExprName -> Expr -> Dot Text -> Identity (Dot Text)
  transformGraph eName _ g =
    let txt = "Ast of " <> T.show eName
     in return $ graphAttrs [Comment txt, textLabel txt] <> g

exprToGraph :: ExprName -> Expr -> DotGraph Text
exprToGraph eName = runIdentity . buildGraph eName