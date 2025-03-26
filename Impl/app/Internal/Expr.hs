module Internal.Expr where

import Data.List.NonEmpty (NonEmpty)
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T

newtype Size = Size Int
  deriving (Eq, Ord, Enum, Num)

newtype ExprId = EId Int
  deriving (Eq, Ord)

instance Show Size where
  show :: Size -> String
  show (Size s) = show s

instance Show ExprId where
  show :: ExprId -> String
  show (EId x) = show x

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

data LeftValue
  = LeftAtom Operand ExprId
  | LeftConcat {args :: NonEmpty LeftValue, concatSize :: Size, concatTag :: ExprId}
  deriving (Show)

data Expr = E {e :: ExprKind, exprTag :: ExprId}
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
  | BinOpAssign LeftValue AssignBinaryOp Expr
  | ShiftAssign LeftValue ShiftBinaryOp Expr
  | Conditional Expr Expr Expr
  | UnaryConcat Expr
  | BinaryConcat Expr Expr
  | Repl Int Expr
  | Inside Expr (NonEmpty Expr)
  deriving (Show)

{-# INLINE exprKind #-}
exprKind :: Expr -> ExprKind
exprKind = e

{-# INLINE leftSize #-}
leftSize :: LeftValue -> Size
leftSize (LeftAtom x _) = opSize x
leftSize (LeftConcat {concatSize}) = concatSize

class ToExprId a where
  exprId :: a -> ExprId

instance ToExprId ExprId where
  {-# INLINE exprId #-}
  exprId :: ExprId -> ExprId
  exprId = id

instance ToExprId Expr where
  {-# INLINE exprId #-}
  exprId :: Expr -> ExprId
  exprId = exprTag

instance ToExprId LeftValue where
  {-# INLINE exprId #-}
  exprId :: LeftValue -> ExprId
  exprId (LeftAtom _ i) = i
  exprId (LeftConcat {concatTag}) = concatTag

instance (ToExprId a, ToExprId b) => ToExprId (Either a b) where
  {-# INLINE exprId #-}
  exprId :: (ToExprId a, ToExprId b) => Either a b -> ExprId
  exprId = either exprId exprId