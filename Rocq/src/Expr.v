From Stdlib Require Import Lists.List.
From Verilog Require Import Utils.

Import ListNotations.
Import Utils.

Module Expr.

  Unset Elimination Schemes.

  Inductive Expr : Type :=
  | EAtom (size: nat)
  | EBinOp (lhs rhs: Expr)
  | EUnOp (arg: Expr)
  | ECast (arg: Expr)
  | EComp (lhs rhs: Expr)
  | ELogic (lhs rhs: Expr)
  | EReduction (arg: Expr)
  | EShift (lhs rhs: Expr)
  | EAssign (lval: nat) (arg: Expr)
  | ECond (cond tb fb: Expr)
  | EConcat (args: list Expr)
  | ERepl (amount: nat) (arg: Expr)
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

  Section Expr_rect.
    Variable P : Expr -> Type.

    Hypothesis HPAtom:
      forall o, P (EAtom o).

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

    Hypothesis HPCond:
      forall cond tb fb, P cond -> P tb -> P fb -> P (ECond cond tb fb).

    Hypothesis HPConcat:
      forall args, (forall n e, nth_error args n = Some e -> P e) -> P (EConcat args).

    Hypothesis HPRepl:
      forall n arg, P arg -> P (ERepl n arg).

    Fixpoint Expr_rect e : P e :=
      match e with
      | EAtom o => HPAtom o
      | EBinOp lhs rhs => HPBinOp _ _ (Expr_rect lhs) (Expr_rect rhs)
      | EUnOp arg => HPUnOp _ (Expr_rect arg)
      | ECast arg => HPCast _ (Expr_rect arg)
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

  Definition Expr_ind (P: Expr -> Prop) := Expr_rect P.
  Definition Expr_rec (P: Expr -> Set) := Expr_rect P.

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
