module Model
  ( Model (),
    Result (..),
    ExprName (),
    ExprTag (),
    buildExpr,
    buildLValue,
    findOperand,
    addOperand,
    isTagUsed,
    addExpr,
    addNamedExpr,
    forEachExpr,
    runModel,
  )
where

import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Internal.Expr

-- data Ast = Ast
--   { exprs :: Map ExprName Expr,
--     tagToId :: Map ExprTag ExprId,
--     idToExpr :: Map ExprId Expr,
--     idToTopLevel :: Set ExprId
--   }
--   deriving (Show)

-- {-# INLINE astExprs #-}
-- astExprs :: Ast -> Map ExprName Expr
-- astExprs = exprs

-- {-# INLINE topLevelExpr #-}
-- topLevelExpr :: Ast -> Expr -> Expr
-- topLevelExpr ast e = (Map.!) (idToExpr ast) . fromJust $ Set.lookupGE (idFromExpr e) (idToTopLevel ast)

-- {-# INLINE exprFromTag #-}
-- exprFromTag :: Ast -> ExprTag -> Expr
-- exprFromTag ast = (Map.!) (idToExpr ast) . (Map.!) (tagToId ast)

data ExprName = EName Text | EInt Int
  deriving (Eq, Ord)

newtype ExprTag = ETag Text
  deriving (Eq, Ord)

instance Show ExprName where
  show :: ExprName -> String
  show (EName x) = T.unpack x
  show (EInt x) = show x

instance Show ExprTag where
  show :: ExprTag -> String
  show (ETag x) = T.unpack x

data Result = Success | Error

data InternalState = S
  { nextId :: ExprId,
    nextExprInt :: Int,
    operands :: Map Text Operand,
    exprs :: Map ExprName Expr,
    tagToId :: Map ExprTag ExprId,
    idToExpr :: Map ExprId Expr,
    idToTopLevel :: Set ExprId
  }

newtype Model a = Model (State InternalState a)
  deriving (Functor, Applicative, Monad)

freshId :: Model ExprId
freshId = Model . state $ \m@S {nextId = i} -> (i, m {nextId = incrId i})
  where
    incrId (EId x) = EId $ x + 1

buildExpr :: ExprKind -> Model Expr
buildExpr eKind = do
  eId <- freshId
  let expr = E eKind eId
  () <- Model . modify $ \m -> m {idToExpr = Map.insert eId expr $ idToExpr m}
  return expr

buildLValue :: (ExprId -> LeftValue) -> Model LeftValue
buildLValue f = freshId >>= return . f

findOperand :: Text -> Model (Maybe Operand)
findOperand t = Model . gets $ Map.lookup t . operands

addOperand :: Operand -> Model Result
addOperand op = Model . state $ \m ->
  case Map.insertLookupWithKey (\_ x _ -> x) (opName op) op (operands m) of
    (Nothing, ops) -> (Success, m {operands = ops})
    (Just _, _) -> (Error, m)

isTagUsed :: Text -> Model (Maybe ExprTag)
isTagUsed tag = do
  let tagId = ETag tag
  tagExist <- Model . gets $ Map.member tagId . tagToId
  return $ if tagExist then Nothing else Just tagId

addExpr :: Expr -> Map ExprTag ExprId -> Model ()
addExpr expr tags = Model . modify $ \m ->
  let eId = nextExprInt m
   in m
        { exprs = Map.insert (EInt eId) expr (exprs m),
          idToTopLevel = Set.insert (exprId expr) $ idToTopLevel m,
          tagToId = tagToId m <> tags,
          nextExprInt = eId + 1
        }

addNamedExpr :: Text -> Expr -> Map ExprTag ExprId -> Model Result
addNamedExpr eName expr tags = Model . state $ \m ->
  case Map.insertLookupWithKey (\_ x _ -> x) (EName eName) expr (exprs m) of
    (Nothing, newExprs) ->
      ( Success,
        m
          { exprs = newExprs,
            idToTopLevel = Set.insert (exprId expr) $ idToTopLevel m,
            tagToId = tagToId m <> tags
          }
      )
    (Just _, _) -> (Error, m)

forEachExpr :: (Monoid c) => (ExprName -> Expr -> c) -> Model c
forEachExpr f = Model . gets $ Map.foldMapWithKey f . exprs

runModel :: Model a -> a
runModel (Model m) =
  let initialState =
        S
          { nextId = EId 0,
            nextExprInt = 0,
            operands = mempty,
            exprs = mempty,
            tagToId = mempty,
            idToExpr = mempty,
            idToTopLevel = mempty
          }
   in evalState m initialState