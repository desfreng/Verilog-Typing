From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Verilog Require Import ident_to_string.
Import ListNotations.

Set Implicit Arguments.

Module Expr.
  Inductive Expr : Type :=
  | EOperand (op: string)
  | EBinOp (lhs rhs: Expr)
  | EUnOp (arg: Expr)
  | ECast (arg: Expr)
  | EComp (lhs rhs: Expr)
  | ELogic (lhs rhs: Expr)
  | EReduction (arg: Expr)
  | EShift (lhs rhs: Expr)
  | EAssign (op: string) (arg: Expr)
  | EShiftAssign (op: string) (arg: Expr)
  | ECond (cond tb fb: Expr)
  | EUnaryConcat (arg: Expr)
  | EBinaryConcat (lhs rhs: Expr)
  | ERepl (amount: nat) (arg: Expr)
  | EInside (arg: Expr) (range: list Expr)
  .
  
  Section Expr_ind_bis.
    Variable P : Expr -> Prop.
    Variable P0 : list Expr -> Prop.
    
    Hypothesis HPOperand:
      forall o, P (EOperand o).
    
    Hypothesis HPBinOp:
      forall lhs rhs, P lhs -> P rhs -> P (EBinOp lhs rhs).
    
    Hypothesis HPUnOp:
      forall arg, P arg -> P (EUnOp arg).

    Hypothesis HPCast:
      forall arg, P arg -> P (ECast arg).

    Hypothesis HPComp:
      forall lhs rhs, P lhs -> P rhs -> P (EComp lhs rhs).

    Hypothesis HPLogic:
      forall lhs rhs, P lhs -> P rhs -> P (ELogic lhs rhs).

    Hypothesis HPReduction:
      forall arg, P arg -> P (EReduction arg).

    Hypothesis HPShift:
      forall lhs rhs, P lhs -> P rhs -> P (EShift lhs rhs).

    Hypothesis HPAssign:
      forall op arg, P arg -> P (EAssign op arg).

    Hypothesis HPShiftAssign:
      forall op arg, P arg -> P (EShiftAssign op arg).

    Hypothesis HPCond:
      forall cond tb fb, P cond -> P tb -> P fb -> P (ECond cond tb fb).

    Hypothesis HPUnConcat:
      forall arg, P arg -> P (EUnaryConcat arg).

    Hypothesis HPBinConcat:
      forall lhs rhs, P lhs -> P rhs -> P (EBinaryConcat lhs rhs).

    Hypothesis HPRepl:
      forall n arg, P arg -> P (ERepl n arg).

    Hypothesis HPInside:
      forall arg range, P arg -> P0 range -> P (EInside arg range).

    Hypothesis HP0Nil:
      P0 [].

    Hypothesis HP0Cons:
      forall hd tl, P hd -> P0 tl -> P0 (hd :: tl).
    
    Fixpoint Expr_ind_bis e : P e.
    Proof.
      destruct e.
      - apply HPOperand.
      - apply HPBinOp. apply Expr_ind_bis. apply Expr_ind_bis.
      - apply HPUnOp. apply Expr_ind_bis.
      - apply HPCast. apply Expr_ind_bis.
      - apply HPComp. apply Expr_ind_bis. apply Expr_ind_bis.
      - apply HPLogic. apply Expr_ind_bis. apply Expr_ind_bis.
      - apply HPReduction. apply Expr_ind_bis.
      - apply HPShift. apply Expr_ind_bis. apply Expr_ind_bis.
      - apply HPAssign. apply Expr_ind_bis.
      - apply HPShiftAssign. apply Expr_ind_bis.
      - apply HPCond. apply Expr_ind_bis. apply Expr_ind_bis. apply Expr_ind_bis.
      - apply HPUnConcat. apply Expr_ind_bis.
      - apply HPBinConcat. apply Expr_ind_bis. apply Expr_ind_bis.
      - apply HPRepl. apply Expr_ind_bis.
      - apply HPInside. apply Expr_ind_bis. induction range.
        + apply HP0Nil.
        + apply HP0Cons. apply Expr_ind_bis. apply IHrange.
     Qed.

   End Expr_ind_bis.

End Expr.


Module Notation.
  Import Expr.
  
  Declare Custom Entry expr.
  Declare Custom Entry expr_var.
  
  Notation "a" := (ident_to_string! a) (in custom expr_var at level 0, a constr at level 0, only parsing).
  Notation "a" := (a) (in custom expr_var at level 0, a constr at level 0, format " a ", only printing).

  Notation "$( x )" := x (in custom expr at level 0, x constr, only parsing).
  Notation "<{ e }>" := e (e custom expr at level 200, only parsing).

  Notation "( x )" := x (in custom expr at level 0, x custom expr).
  Notation "x" := (EOperand x) (in custom expr at level 0, x custom expr_var at level 0).
  Notation "x + y" := (EBinOp x y) (in custom expr at level 50, left associativity).
  Notation "- x" := (EUnOp x) (in custom expr at level 0).
  Notation "'signed' ( x )" := (ECast x) (in custom expr at level 0).
  Notation "x == y" := (EComp x y) (in custom expr at level 70, left associativity).
  Notation "x && y" := (ELogic x y) (in custom expr at level 80, left associativity).
  Notation "& x" := (EReduction x) (in custom expr at level 0).
  Notation "x >> y" := (EShift x y) (in custom expr at level 60, left associativity).
  Notation "'set' x := y" := (EAssign x y) (in custom expr at level 95, x custom expr_var, y custom expr, no associativity).
  Notation "x ? y : z" := (ECond x y z) (in custom expr at level 90, right associativity).
  Notation "{ x , y }" := (EBinaryConcat x y) (in custom expr at level 0, x custom expr, y custom expr).
  Notation "{ x }" := (EUnaryConcat x) (in custom expr at level 0, x custom expr).
  Notation "[ i | x ]" := (ERepl i x) (in custom expr at level 0, i constr, x custom expr).

End Notation.

