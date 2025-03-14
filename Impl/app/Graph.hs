{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

module Graph
  ( ExprToGraph (tagText, nodeAttr, edgesAttr, transformGraph, buildGraph),
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

numChildren :: (Foldable t) => [(Text, Expr)] -> t Expr -> [(Text, Expr)]
numChildren beg l = snd $ foldl addChild (0, beg) l
  where
    addChild :: (Int, [(Text, Expr)]) -> Expr -> (Int, [(Text, Expr)])
    addChild (argId, acc) e = (argId + 1, ("arg" <> T.show argId, e) : acc)

children :: ExprKind -> [(Text, Expr)]
children (Operand _) = mempty
children (IntegerValue _) = mempty
children (Arithmetic _ lhs rhs) = [("lhs", lhs), ("rhs", rhs)]
children (PreUnOp _ arg) = [("arg", arg)]
children (PostUnOp _ arg) = [("arg", arg)]
children (Cast _ arg) = [("arg", arg)]
children (Comparison _ lhs rhs) = [("lhs", lhs), ("rhs", rhs)]
children (LogicNot arg) = [("arg", arg)]
children (Logic _ lhs rhs) = [("lhs", lhs), ("rhs", rhs)]
children (Reduction _ arg) = [("arg", arg)]
children (Shift _ lhs rhs) = [("lhs", lhs), ("rhs", rhs)]
children (Pow lhs rhs) = [("lhs", lhs), ("rhs", rhs)]
children (BinOpAssign v _ expr) = [("var", v), ("expr", expr)]
children (ShiftAssign v _ expr) = [("var", v), ("expr", expr)]
children (Conditional cond tBranch fBranch) =
  [("cond", cond), ("true", tBranch), ("false", fBranch)]
children (Concat l) = numChildren [] l
children (ReplConcat _ l) = numChildren [] l
children (Inside arg l) = numChildren [("item", arg)] l

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

class (Monad m) => ExprToGraph m where
  tagText :: Expr -> Text -> m Text
  nodeAttr :: ExprId -> m Attributes
  edgesAttr :: ExprId -> ExprId -> m Attributes
  transformGraph :: ExprName -> Expr -> Dot ExprId -> m (Dot ExprId)

  addAstEdge :: ExprId -> (Text, Expr) -> m (Dot ExprId)
  addAstEdge parentId (edgeName, childExpr) =
    let childId = idFromExpr childExpr
     in do
          edgeCustomAttr <- (textLabel edgeName :) <$> edgesAttr parentId childId
          return $ edge parentId childId $ edgeCustomAttr

  buildExprGraph :: Expr -> m (Dot ExprId)
  buildExprGraph expr =
    let exprId = idFromExpr expr
        eKind = exprKind expr
        c = children eKind
     in do
          nodeLabel <- tagText expr (exprLabel eKind)
          nodeCustomAttr <- (textLabel nodeLabel :) <$> nodeAttr exprId
          edgesDef <- mconcat <$> mapM (addAstEdge exprId) c
          childDefs <- mconcat <$> mapM (buildExprGraph . snd) c
          return $ node exprId nodeCustomAttr <> edgesDef <> childDefs

  buildGraph :: ExprName -> Expr -> m (DotGraph ExprId)
  buildGraph eName expr =
    digraph' <$> (buildExprGraph expr >>= transformGraph eName expr)

instance ExprToGraph Identity where
  tagText :: Expr -> Text -> Identity Text
  tagText expr txt =
    return $ case exprKind expr of
      Operand (Op {opSize}) -> txt <> "\nsize:" <> T.show opSize
      _ -> txt

  nodeAttr :: ExprId -> Identity Attributes
  nodeAttr _ = pure []

  edgesAttr :: ExprId -> ExprId -> Identity Attributes
  edgesAttr _ _ = pure []

  transformGraph :: ExprName -> Expr -> Dot ExprId -> Identity (Dot ExprId)
  transformGraph eName _ g =
    let txt = T.show eName
     in return $ graphAttrs [Comment $ "Graph for " <> txt, textLabel $ "Graph for " <> txt] <> g

exprToGraph :: ExprName -> Expr -> DotGraph ExprId
exprToGraph eName = runIdentity . buildGraph eName