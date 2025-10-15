From Stdlib Require Import Lists.List.
From Verilog Require Import Utils.

Import ListNotations.
Import Utils.

(** This module defines the untyped abstract syntax tree (AST) of SystemVerilog expressions. *)
Module Expr.

  Unset Elimination Schemes.

  (** ** SystemVerilog Expression Model *)
  (** This inductive type represents the structure of SystemVerilog expressions
      before typing. *)
  Inductive Expr : Type :=
  | EOperand (size: nat)
      (** Atomic operand, storing its bitwidth [size] (as determined by the Gamma function). *)
  | EBinOp (lhs rhs: Expr)
      (** Binary operator expression. *)
  | EUnOp (arg: Expr)
      (** Unary operator expression. *)
  | EComp (lhs rhs: Expr)
      (** Comparison expression (e.g., equality, inequality, relational ops). *)
  | ELogic (lhs rhs: Expr)
      (** Logical expression (e.g., logical AND, OR). *)
  | EReduction (arg: Expr)
      (** Reduction expression (e.g., bitwise reduction operators). *)
  | EShift (lhs rhs: Expr)
      (** Bitwise shift operation (e.g., left/right shift). *)
  | EAssign (lval: nat) (arg: Expr)
      (** Assignment expression, storing the size of the left-hand value [lval]. *)
  | ECond (cond tb fb: Expr)
      (** Conditional (ternary) expression: [cond ? tb : fb]. *)
  | EConcat (args: list Expr)
      (** Concatenation of multiple subexpressions. *)
  | ERepl (amount: nat) (arg: Expr)
      (** Replication operator: repeats [arg] [amount] times. *)
  .

  Set Elimination Schemes.

  Lemma HNil: forall (P: Expr -> Type) n e, nth_error [] n = Some e -> P e.
  Proof. intros; rewrite nth_error_nil in H; inv H. Qed.

  Lemma HCons: forall (P: Expr -> Type) hd tl,
      P hd -> (forall n e, nth_error tl n = Some e -> P e) ->
      forall n e, nth_error (hd :: tl) n = Some e -> P e.
  Proof.
    intros; destruct n; inv H.
    - apply X.
    - apply (X0 _ _ H1).
  Qed.

  (** ** Custom Induction Principle for [Expr] *)
  
  (** Since the built-in elimination scheme is not sufficient for lists of
      expressions (e.g., [EConcat]), we define a custom induction principle that
      handles list substructures recursively. *)
  Section Expr_rect.
    Variable P : Expr -> Type.

    Hypothesis HPAtom:
      forall o, P (EOperand o).

    Hypothesis HPBinOp:
      forall lhs rhs, P lhs -> P rhs -> P (EBinOp lhs rhs).

    Hypothesis HPUnOp:
      forall arg, P arg -> P (EUnOp arg).

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

    Hypothesis HPCond:
      forall cond tb fb, P cond -> P tb -> P fb -> P (ECond cond tb fb).

    Hypothesis HPConcat:
      forall args, (forall n e, nth_error args n = Some e -> P e) -> P (EConcat args).

    Hypothesis HPRepl:
      forall n arg, P arg -> P (ERepl n arg).

    (** Recursive definition of [Expr_rect], extending the induction principle
        to handle list structures (notably in [EConcat]). *)
    Fixpoint Expr_rect e : P e :=
      match e with
      | EOperand o => HPAtom o
      | EBinOp lhs rhs => HPBinOp _ _ (Expr_rect lhs) (Expr_rect rhs)
      | EUnOp arg => HPUnOp _ (Expr_rect arg)
      | EComp lhs rhs => HPComp _ _ (Expr_rect lhs) (Expr_rect rhs)
      | ELogic lhs rhs => HPLogic _ _ (Expr_rect lhs) (Expr_rect rhs)
      | EReduction arg => HPReduction _ (Expr_rect arg)
      | EShift lhs rhs => HPShift _ _ (Expr_rect lhs) (Expr_rect rhs)
      | EAssign lval arg => HPAssign lval _ (Expr_rect arg)
      | ECond arg lhs rhs =>
          HPCond _ _ _ (Expr_rect arg) (Expr_rect lhs) (Expr_rect rhs)
      | EConcat args => HPConcat args
                           ((list_rect _ (HNil _)
                               (fun hd tl => HCons _ _ tl (Expr_rect hd)))
                              args)
      | ERepl n arg => HPRepl n _ (Expr_rect arg)
      end
    .
  End Expr_rect.

  (** Convenient versions of [Expr_rect] for properties and sets. *)
  Definition Expr_ind (P: Expr -> Prop) := Expr_rect P.
  Definition Expr_rec (P: Expr -> Set) := Expr_rect P.

  (** ** Decidability of Expression Equality *)
  (** Equality between two [Expr] terms is decidable by structural comparison. *)
  Theorem Expr_eq_dec : forall (e f: Expr), {e = f} + {e <> f}.
  Proof.
    intros. decide equality.
    - decide equality.
    - decide equality.
    - generalize dependent args0. induction args.
      + destruct args0. left. reflexivity. right. congruence.
      + destruct args0. right. congruence. destruct (H 0 a (eq_refl _) e0).
        * edestruct IHargs with (args0 := args0). intros n. apply (H (S n)). subst.
          auto. right. congruence.
        * right. congruence.
    - decide equality.
  Qed.
End Expr.
