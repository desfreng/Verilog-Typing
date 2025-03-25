{-# LANGUAGE OverloadedStrings #-}

module Context.Graph (contextGraphs) where

import Context.Context
import Control.Monad.Reader
import Data.Foldable
import Data.GraphViz.Attributes hiding (bgColor)
import Data.GraphViz.Attributes.Complete hiding (Size)
import Data.GraphViz.Types.Monadic (Dot, GraphID (..), cluster, edge, graphAttrs, node)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Expr
import Graph
import Model

newtype ContextAst a = ContextAst {runContextAst :: Reader ExprContext a}
  deriving (Functor, Applicative, Monad, MonadReader ExprContext)

instance (Semigroup a) => Semigroup (ContextAst a) where
  (<>) :: (Semigroup a) => ContextAst a -> ContextAst a -> ContextAst a
  (<>) = liftA2 (<>)

instance (Monoid a) => Monoid (ContextAst a) where
  mempty :: (Monoid a) => ContextAst a
  mempty = pure mempty

contextDepGraph :: ExprName -> ContextAst (Dot Text)
contextDepGraph eName = do
  ctx <- contexts
  g <- Map.foldMapWithKey addCtx ctx
  let txt = "Context Dependencies of " <> T.show eName
  return $ graphAttrs [Comment txt, textLabel txt] <> g
  where
    addCtx :: ContextId -> Context -> ContextAst (Dot Text)
    addCtx ctxId ctxVal =
      do
        bg <- contextColor Nothing ctxId
        let attrs = textLabel ("Context " <> T.show ctxId) : colorNode bg
        let ctxNode = node (nPrefix ctxId) attrs
        let edgesList = foldMap (addEdge ctxId) ctxVal
        return $ ctxNode <> edgesList

    addEdge _ (Atom _ _) = mempty
    addEdge pId (CastDep cId _) = edge (nPrefix pId) (nPrefix cId) [textLabel "cast"]
    addEdge pId (ConcatDep l) = foldMap (\(cId, _) -> edge (nPrefix pId) (nPrefix cId) [textLabel "concat"]) l
    addEdge pId (ReplDep _ l) = foldMap (\(cId, _) -> edge (nPrefix pId) (nPrefix cId) [textLabel "repl"]) l

    nPrefix eId = "dep_" <> T.show eId

instance ExprToGraph ContextAst where
  prefix :: ExprId -> ContextAst Text
  prefix eId = return $ "ctx_" <> T.show eId

  exprText :: Expr -> Text -> ContextAst Text
  exprText expr lbl = do
    c <- exprSize $ exprId expr
    return $ lbl <> "\nsize: " <> T.show c

  exprAttr :: ExprId -> ContextAst Attributes
  exprAttr eId = do
    c <- exprContext eId
    ctxCol <- contextColor Nothing c
    return $ colorNode ctxCol

  lValueText :: LeftValue -> Text -> ContextAst Text
  lValueText lValue txt = return $ txt <> "\nsize: " <> T.show (leftSize lValue)

  lValueAttr :: ExprId -> ContextAst Attributes
  lValueAttr _ = return [Style [SItem Dashed []]]

  edgesAttr :: ExprId -> ExprId -> ContextAst Attributes
  edgesAttr _ _ = pure []

  transformGraph :: ExprName -> Expr -> Dot Text -> ContextAst (Dot Text)
  transformGraph eName _ g = do
    let txt = "Ast with Clusters of " <> T.show eName
    let depTxt = "Clusters Dependencies"
    depG <- contextDepGraph eName
    let gDep = cluster (Str "") $ graphAttrs [Comment depTxt, textLabel depTxt] <> depG
    return $ gDep <> graphAttrs [Comment txt, textLabel txt] <> g

contextAstGraph :: ExprName -> Expr -> ExprContext -> Dot Text
contextAstGraph eName e eCtx = runReader (runContextAst $ buildGraph eName e) eCtx

data CtxKind = AtomKind | CastDepKind | ConcatDepKind | ReplDepKind

data ContextDisplayInfo = CtxDisplayInfo
  { ctxId :: ContextId,
    exprStatus :: Map ExprId CtxKind,
    exprCtx :: ExprContext
  }

newtype ContextDisplay a = ContextDisplay {runContextDisplay :: Reader ContextDisplayInfo a}
  deriving (Functor, Applicative, Monad)

instance MonadReader ExprContext ContextDisplay where
  ask :: ContextDisplay ExprContext
  ask = ContextDisplay . asks $ exprCtx

  local :: (ExprContext -> ExprContext) -> ContextDisplay a -> ContextDisplay a
  local f (ContextDisplay x) = ContextDisplay $ local (\s -> s {exprCtx = f $ exprCtx s}) x

inCtxColor :: Color
inCtxColor = RGB 200 200 200

atomColor :: Color
atomColor = RGB 255 78 77

castColor :: Color
castColor = RGB 253 178 0

concatColor :: Color
concatColor = RGB 2 232 137

replColor :: Color
replColor = RGB 2 75 235

legend :: ContextId -> Dot Text
legend cId = cluster (Str "legend") $ do
  graphAttrs [Comment "Legend", textLabel "Legend"]
  node (T.show cId <> "_in_ctx") $ [Shape BoxShape, textLabel "In Context"] <> colorNode inCtxColor
  node (T.show cId <> "_atom") $ [Shape BoxShape, textLabel "Atom"] <> colorNode atomColor
  node (T.show cId <> "_cast") $ [Shape BoxShape, textLabel "Cast Dependency"] <> colorNode castColor
  node (T.show cId <> "_concat") $ [Shape BoxShape, textLabel "Concat Dependency"] <> colorNode concatColor
  node (T.show cId <> "_repl") $ [Shape BoxShape, textLabel "Repl Dependency"] <> colorNode replColor

instance ExprToGraph ContextDisplay where
  prefix :: ExprId -> ContextDisplay Text
  prefix eId = do
    cId <- ContextDisplay . asks $ ctxId
    return $ "ctx_" <> T.show cId <> "_" <> T.show eId

  exprText :: Expr -> Text -> ContextDisplay Text
  exprText expr lbl = do
    c <- exprSize $ exprId expr
    return $ lbl <> "\nsize: " <> T.show c

  exprAttr :: ExprId -> ContextDisplay Attributes
  exprAttr eId = do
    nKind <- ContextDisplay . asks $ Map.lookup eId . exprStatus
    bgCol <- case nKind of
      Nothing -> do
        eCid <- exprContext eId
        cId <- ContextDisplay . asks $ ctxId
        if eCid == cId
          then return $ inCtxColor
          else contextColor (Just 0.1) eCid
      Just AtomKind -> return atomColor
      Just CastDepKind -> return castColor
      Just ConcatDepKind -> return concatColor
      Just ReplDepKind -> return replColor
    return $ colorNode bgCol

  lValueText :: LeftValue -> Text -> ContextDisplay Text
  lValueText lValue txt = return $ txt <> "\nsize: " <> T.show (leftSize lValue)

  lValueAttr :: ExprId -> ContextDisplay Attributes
  lValueAttr _ = return [Style [SItem Dashed []]]

  edgesAttr :: ExprId -> ExprId -> ContextDisplay Attributes
  edgesAttr _ _ = pure []

  transformGraph :: ExprName -> Expr -> Dot Text -> ContextDisplay (Dot Text)
  transformGraph eName _ g = do
    cId <- ContextDisplay . asks $ ctxId
    let txt = "Cluster " <> T.show cId <> " in " <> T.show eName
    return $ graphAttrs [Comment txt, textLabel txt] <> g <> legend cId

graphContext :: ExprName -> Expr -> ExprContext -> ContextId -> Dot Text
graphContext eName e eCtx cId = runReader (runContextDisplay $ buildGraph eName e) ctxInfo
  where
    ctxInfo =
      let status = foldMap go $ getContext eCtx cId
       in CtxDisplayInfo
            { ctxId = cId,
              exprStatus = status,
              exprCtx = eCtx
            }

    go (Atom _ eId) = Map.singleton eId AtomKind
    go (CastDep _ eId) = Map.singleton eId CastDepKind
    go (ConcatDep l) = foldMap (\(_, eId) -> Map.singleton eId ConcatDepKind) l
    go (ReplDep _ l) = foldMap (\(_, eId) -> Map.singleton eId ConcatDepKind) l

contextGraphs :: ExprName -> Expr -> Dot Text
contextGraphs eName e =
  let ctx = buildExprContext e
      ctxAstG = contextAstGraph eName e ctx
      ctxGs = (\cId -> (cId, graphContext eName e ctx cId)) <$> toList (getCtxIds ctx)
   in do
        cluster (Str $ "Context Ast of " <> T.show eName) ctxAstG
        -- cluster (Str $ "Context Dependencies of " <> T.show eName) ctxDegG
        mapM_ (\(cId, g) -> cluster (Str $ "Context " <> T.show cId) g) ctxGs
