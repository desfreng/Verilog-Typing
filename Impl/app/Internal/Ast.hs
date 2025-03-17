module Internal.Ast where

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

newtype AstId = AId Int
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

instance Show AstId where
  show :: AstId -> String
  show (AId x) = show x

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
  = LeftAtom Operand AstId
  | LeftConcat {args :: [LeftValue], concatSize :: Size, concatTag :: AstId}
  deriving (Show)

data Expr = E {getExpr :: ExprKind, astTag :: AstId}
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
  | Concat [Expr]
  | ReplConcat Int [Expr]
  | Inside Expr [Expr]
  deriving (Show)

data Ast = Ast
  { exprs :: Map ExprName Expr,
    tagToId :: Map ExprTag AstId,
    idToExpr :: Map AstId Expr,
    idToTopLevel :: Set AstId
  }
  deriving (Show)

{-# INLINE astExprs #-}
astExprs :: Ast -> Map ExprName Expr
astExprs = exprs

{-# INLINE idFromExpr #-}
idFromExpr :: Expr -> AstId
idFromExpr = astTag

{-# INLINE exprKind #-}
exprKind :: Expr -> ExprKind
exprKind = getExpr

{-# INLINE topLevelExpr #-}
topLevelExpr :: Ast -> Expr -> Expr
topLevelExpr ast e = (Map.!) (idToExpr ast) . fromJust $ Set.lookupGE (idFromExpr e) (idToTopLevel ast)

{-# INLINE exprFromTag #-}
exprFromTag :: Ast -> ExprTag -> Expr
exprFromTag ast = (Map.!) (idToExpr ast) . (Map.!) (tagToId ast)

{-# INLINE leftSize #-}
leftSize :: LeftValue -> Size
leftSize (LeftAtom x _) = opSize x
leftSize (LeftConcat {concatSize}) = concatSize

{-# INLINE idFromLValue #-}
idFromLValue :: LeftValue -> AstId
idFromLValue (LeftAtom _ i) = i
idFromLValue (LeftConcat {concatTag}) = concatTag