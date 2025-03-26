{-# LANGUAGE OverloadedStrings #-}

module Context.Context
  ( ContextId (),
    ContextElm (..),
    Context (),
    ExprContext (),
    buildExprContext,
    exprContext,
    contexts,
    getCtxIds,
    exprSize,
    contextColor,
    getContext,
  )
where

import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable
import Data.GraphViz.Attributes.Colors (Color (HSV))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import Expr

newtype ContextId = CId Int
  deriving (Eq, Ord)

instance Show ContextId where
  show :: ContextId -> String
  show (CId x) = show x

data ContextElm
  = IdDep ContextId ExprId
  | AddDep {lhsCtx :: ContextId, lhsExpr :: ExprId, rhsCtx :: ContextId, rhsExpr :: ExprId}
  | MulDep Int ContextId ExprId
  | Atom Size ExprId
  deriving (Eq, Ord)

type Context = Set ContextElm

sizeOne :: Size
sizeOne = (Size 1)

ctxToDouble :: ContextId -> Double
ctxToDouble (CId x) = fromIntegral x

data ExprContext = ExprContext
  { endCtx :: ContextId,
    ctxVal :: Map ContextId Context,
    exprCtx :: Map ExprId ContextId,
    ctxSize :: Map ContextId Size
  }

getContext :: ExprContext -> ContextId -> Context
getContext = (Map.!) . ctxVal

contextColor :: (MonadReader ExprContext m) => Maybe Double -> ContextId -> m Color
contextColor s x = do
  maxCtx <- asks endCtx
  let h = ctxToDouble x / ctxToDouble maxCtx
  return $ HSV h (fromMaybe 1 s) 1

contexts :: (MonadReader ExprContext m) => m (Map ContextId Context)
contexts = asks ctxVal

getCtxIds :: ExprContext -> Set ContextId
getCtxIds = Map.keysSet . ctxVal

exprContext :: (MonadReader ExprContext m) => ExprId -> m ContextId
exprContext e = asks $ \s -> fromMaybe (error "No Expr ?") $ Map.lookup e (exprCtx s)

exprSize :: (MonadReader ExprContext m) => ExprId -> m Size
exprSize e = do
  cId <- exprContext e
  asks $ \s -> (Map.!) (ctxSize s) cId

data Ctx = Ctx
  { nextContext :: ContextId,
    contextVal :: Map ContextId Context,
    exprContexts :: Map ExprId ContextId
  }

type CtxState = State Ctx

(|->) :: Expr -> ContextId -> CtxState ()
e |-> c = modify $ \s -> s {exprContexts = Map.insert (exprId e) c $ exprContexts s}

freshContext :: CtxState ContextId
freshContext = state $ \s ->
  let cId = nextContext s
   in (cId, s {nextContext = incrCtx cId})
  where
    incrCtx (CId i) = CId $ i + 1

freshContextWith :: ContextElm -> CtxState ContextId
freshContextWith e = do
  c <- freshContext
  c <=| e
  return c

(<=|) :: ContextId -> ContextElm -> CtxState ()
ctx <=| elm = modify $ \s ->
  let ctxSet = fromMaybe mempty $ Map.lookup ctx (contextVal s)
      newCtxSet = Set.insert elm ctxSet
   in s {contextVal = Map.insert ctx newCtxSet $ contextVal s}

atom :: (ToExprId a) => Size -> a -> ContextElm
atom s = Atom s . exprId

idDep :: ContextId -> Expr -> ContextElm
idDep s = IdDep s . exprId

addDep :: (ContextId, Expr) -> (ContextId, Expr) -> ContextElm
addDep lhs rhs =
  AddDep
    { lhsCtx = fst lhs,
      lhsExpr = exprId $ snd lhs,
      rhsCtx = fst rhs,
      rhsExpr = exprId $ snd rhs
    }

mulDep :: Int -> ContextId -> Expr -> ContextElm
mulDep i c = MulDep i c . exprId

(|-) :: Expr -> ContextId -> CtxState ()
e |- c =
  childrenContext (exprKind e)
  where
    childrenContext (Operand (Op {opSize})) = do
      c <=| atom opSize e
      ------------------------------
      e |-> c
    childrenContext (IntegerValue (VInteger {size})) = do
      c <=| atom size e
      ------------------------------
      e |-> c
    childrenContext (Arithmetic _ lhs rhs) = do
      lhs |- c
      rhs |- c
      ------------------------------
      e |-> c
    childrenContext (PreUnOp _ arg) = do
      arg |- c
      ------------------------------
      e |-> c
    childrenContext (PostUnOp _ arg) = do
      arg |- c
      ------------------------------
      e |-> c
    childrenContext (LogicNot arg) = do
      c' <- freshContext
      arg |- c'
      c <=| atom sizeOne e
      ------------------------------
      e |-> c
    childrenContext (Cast _ arg) = do
      c' <- freshContext
      arg |- c'
      c <=| idDep c' arg
      ------------------------------
      e |-> c
    childrenContext (Comparison _ lhs rhs) = do
      c' <- freshContext
      lhs |- c'
      rhs |- c'
      c <=| atom sizeOne e
      ------------------------------
      e |-> c
    childrenContext (Logic _ lhs rhs) = do
      c' <- freshContext
      lhs |- c'
      c'' <- freshContext
      rhs |- c''
      c <=| atom sizeOne e
      ------------------------------
      e |-> c
    childrenContext (Reduction _ arg) = do
      c' <- freshContext
      arg |- c'
      c <=| atom sizeOne e
      ------------------------------
      e |-> c
    childrenContext (Shift _ lhs rhs) = do
      lhs |- c
      c' <- freshContext
      rhs |- c'
      ------------------------------
      e |-> c
    childrenContext (Pow lhs rhs) = do
      lhs |- c
      c' <- freshContext
      rhs |- c'
      ------------------------------
      e |-> c
    childrenContext (BinOpAssign lhs _ expr) = do
      let s = leftSize lhs
      c <=| atom s e
      c' <- freshContextWith $ atom s lhs
      expr |- c'
      ------------------------------
      e |-> c
    childrenContext (ShiftAssign lhs _ expr) = do
      let s = leftSize lhs
      c <=| atom s e
      c' <- freshContext
      expr |- c'
      ------------------------------
      e |-> c
    childrenContext (Conditional cond tBranch fBranch) = do
      c' <- freshContext
      cond |- c'
      tBranch |- c
      fBranch |- c
      ------------------------------
      e |-> c
    childrenContext (UnaryConcat arg) = do
      c' <- freshContext
      arg |- c'
      c <=| idDep c' arg
      ------------------------------
      e |-> c
    childrenContext (BinaryConcat lhs rhs) = do
      cLhs <- freshContext
      lhs |- cLhs
      cRhs <- freshContext
      rhs |- cRhs
      c <=| addDep (cLhs, lhs) (cRhs, rhs)
      ------------------------------
      e |-> c
    childrenContext (Repl i arg) = do
      c' <- freshContext
      arg |- c'
      c <=| mulDep i c' arg
      ------------------------------
      e |-> c
    childrenContext (Inside arg l) = do
      c' <- freshContext
      arg |- c'
      mapM_ (\e_i -> e_i |- c') l
      c <=| atom sizeOne e
      ------------------------------
      e |-> c

buildExprContext :: Expr -> ExprContext
buildExprContext e =
  let initialGCInfo =
        Ctx
          { nextContext = CId 0,
            contextVal = mempty,
            exprContexts = mempty
          }
      s =
        execState
          ( do
              c <- freshContext
              e |- c
          )
          initialGCInfo
      m = evalState (runReaderT (mapM solveCtx (contextVal s)) s) mempty
   in ExprContext
        { endCtx = nextContext s,
          ctxVal = contextVal s,
          exprCtx = exprContexts s,
          ctxSize = m
        }

type CtxSolver = ReaderT Ctx (State (Map ContextId Size))

solveCtx :: Context -> CtxSolver Size
solveCtx ctx = do
  ctxSize <-
    foldlM
      ( \s elm -> do
          elmSize <- findSize elm
          return $ max elmSize s
      )
      (Size 0)
      ctx
  return ctxSize
  where
    contextSize :: ContextId -> CtxSolver Size
    contextSize cId = do
      ex <- gets $ \m -> Map.lookup cId m
      case ex of
        Just s -> return s
        Nothing -> do
          c <- asks $ \c -> (Map.!) (contextVal c) cId
          finalS <- solveCtx c
          modify $ \m -> Map.insert cId finalS m
          return finalS

    findSize :: ContextElm -> CtxSolver Size
    findSize (Atom s _) = return s
    findSize (IdDep depId _) = contextSize depId
    findSize (AddDep {lhsCtx, rhsCtx}) = (+) <$> contextSize lhsCtx <*> contextSize rhsCtx
    findSize (MulDep i depId _) = (* Size i) <$> contextSize depId