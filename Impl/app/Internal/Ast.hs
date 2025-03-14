module Internal.Ast where

import Data.GraphViz.Printing (DotCode, PrintDot (unqtDot))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T

newtype Size = Size Int
  deriving (Eq, Ord, Enum, Num)

newtype ExprName = EName Text
  deriving (Eq, Ord)

newtype ExprTag = ETag Text
  deriving (Eq, Ord)

newtype ExprId = EId Int
  deriving (Eq, Ord)

instance Show Size where
  show :: Size -> String
  show (Size s) = show s

instance Show ExprName where
  show :: ExprName -> String
  show (EName x) = T.unpack x

instance Show ExprTag where
  show :: ExprTag -> String
  show (ETag x) = T.unpack x

instance Show ExprId where
  show :: ExprId -> String
  show (EId x) = show x

instance PrintDot ExprId where
  unqtDot :: ExprId -> DotCode
  unqtDot (EId x) = unqtDot x

data Operand = Op {opName :: Text, opSize :: Size}
  deriving (Eq, Ord)

instance Show Operand where
  show :: Operand -> String
  show Op {opName} = T.unpack opName

data VerilogInteger = VInteger {size :: Size, value :: Integer}

instance Show VerilogInteger where
  show :: VerilogInteger -> String
  show VInteger {size, value} = show size <> "'d" <> show value

data ArithBinaryOp
  = Addition
  | Subtraction
  | Multiplication
  | Division
  | Remainder
  | BinaryAnd
  | BinaryOr
  | BinaryXor
  | BinaryNXor
  deriving (Show)

data CompBinaryOp = Lt | Le | Eq | Neq | Gt | Ge | WildEq | WildNeq | StrictEq | StrictNeq
  deriving (Show)

data LogicBinaryOp = And | Or | Impl | Equiv
  deriving (Show)

data ShiftBinaryOp = ArithLeft | ArithRight | LogicLeft | LogicRight
  deriving (Show)

data AssignBinaryOp
  = None
  | AdditionAssign
  | SubtractionAssign
  | MultiplicationAssign
  | DivisionAssign
  | RemainderAssign
  | LogicalAndAssign
  | LogicalOrAssign
  | LogicalXorAssign
  deriving (Show)

data PreUnaryOp = Negate | PreIncr | PreDecr | Invert
  deriving (Show)

data PostUnaryOp = PostIncr | PostDecr
  deriving (Show)

data ReductionUnaryOp = RedAnd | RedNand | RedOr | RedNor | RedXor | RedNxor
  deriving (Show)

data Signedness = Signed | Unsigned
  deriving (Show)

data Expr = E {getExpr :: ExprKind, getTag :: ExprId}
  deriving (Show)

data ExprKind
  = Operand Operand
  | IntegerValue VerilogInteger
  | Arithmetic ArithBinaryOp Expr Expr
  | PreUnOp PreUnaryOp Expr
  | PostUnOp PostUnaryOp Expr
  | Cast Signedness Expr
  | Comparison CompBinaryOp Expr Expr
  | LogicNot Expr
  | Logic LogicBinaryOp Expr Expr
  | Reduction ReductionUnaryOp Expr
  | Shift ShiftBinaryOp Expr Expr
  | Pow Expr Expr
  | BinOpAssign Expr AssignBinaryOp Expr
  | ShiftAssign Expr ShiftBinaryOp Expr
  | Conditional Expr Expr Expr
  | Concat [Expr]
  | ReplConcat Int [Expr]
  | Inside Expr [Expr]
  deriving (Show)

data Ast = Ast
  { exprs :: Map ExprName Expr,
    tagToId :: Map ExprTag ExprId,
    idToExpr :: Map ExprId Expr,
    idToTopLevel :: Set ExprId
  }
  deriving (Show)

{-# INLINE astExprs #-}
astExprs :: Ast -> Map ExprName Expr
astExprs = exprs

{-# INLINE exprFromId #-}
exprFromId :: Ast -> ExprId -> Expr
exprFromId = (Map.!) . idToExpr

{-# INLINE idFromExpr #-}
idFromExpr :: Expr -> ExprId
idFromExpr = getTag

{-# INLINE exprKind #-}
exprKind :: Expr -> ExprKind
exprKind = getExpr

{-# INLINE topLevelExpr #-}
topLevelExpr :: Ast -> Expr -> Expr
topLevelExpr ast e = exprFromId ast . fromJust $ Set.lookupGE (idFromExpr e) (idToTopLevel ast)

{-# INLINE exprFromTag #-}
exprFromTag :: Ast -> ExprTag -> Expr
exprFromTag ast = exprFromId ast . (Map.!) (tagToId ast)
