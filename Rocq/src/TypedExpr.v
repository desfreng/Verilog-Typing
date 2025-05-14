From Stdlib Require Import Lists.List.

From Verilog Require Import Utils.

Import ListNotations.

Import Utils.

Module TypedExpr.

  Unset Elimination Schemes.

  Inductive TypedExpr : Type :=
  | TAtom (size origSize: nat)
  | TBinOp (size: nat) (lhs rhs: TypedExpr)
  | TUnOp (size: nat) (arg: TypedExpr)
  | TCast (size: nat) (arg: TypedExpr)
  | TComp (size: nat) (lhs rhs: TypedExpr)
  | TLogic (size: nat) (lhs rhs: TypedExpr)
  | TReduction (size: nat) (arg: TypedExpr)
  | TShift (size: nat) (lhs rhs: TypedExpr)
  | TAssign (size lval: nat) (arg: TypedExpr)
  | TShiftAssign (size lval: nat) (arg: TypedExpr)
  | TCond (size: nat) (cond tb fb: TypedExpr)
  | TConcat (size: nat) (args: list TypedExpr)
  | TRepl (size amount: nat) (arg: TypedExpr)
  .

  Set Elimination Schemes.

  Section TypedExpr_ind.
    Variable P : TypedExpr -> Prop.

    Hypothesis HPAtom:
      forall s o, P (TAtom s o).

    Hypothesis HPBinOp:
      forall s lhs rhs, P lhs -> P rhs -> P (TBinOp s lhs rhs).

    Hypothesis HPUnOp:
      forall s arg, P arg -> P (TUnOp s arg).

    Hypothesis HPCast:
      forall s arg, P arg -> P (TCast s arg).

    Hypothesis HPComp:
      forall s lhs rhs, P lhs -> P rhs -> P (TComp s lhs rhs).

    Hypothesis HPLogic:
      forall s lhs rhs, P lhs -> P rhs -> P (TLogic s lhs rhs).

    Hypothesis HPReduction:
      forall s arg, P arg -> P (TReduction s arg).

    Hypothesis HPShift:
      forall s lhs rhs, P lhs -> P rhs -> P (TShift s lhs rhs).

    Hypothesis HPAssign:
      forall s op arg, P arg -> P (TAssign s op arg).

    Hypothesis HPShiftAssign:
      forall s op arg, P arg -> P (TShiftAssign s op arg).

    Hypothesis HPCond:
      forall s cond tb fb, P cond -> P tb -> P fb -> P (TCond s cond tb fb).

    Hypothesis HPConcat:
      forall s args, (forall n e, nth_error args n = Some e -> P e) -> P (TConcat s args).

    Hypothesis HPRepl:
      forall s n arg, P arg -> P (TRepl s n arg).

    Lemma HNil: forall n e, nth_error [] n = Some e -> P e.
    Proof. intros; destruct n; inv H. Qed.

    Lemma HCons: forall hd tl,
        P hd -> (forall n e, nth_error tl n = Some e -> P e) ->
        forall n e, nth_error (hd :: tl) n = Some e -> P e.
    Proof.
      intros; destruct n; inv H1.
      - apply H.
      - apply (H0 _ _ H3).
    Qed.

    Fixpoint TypedExpr_ind e : P e :=
      match e with
      | TAtom s o => HPAtom s o
      | TBinOp s lhs rhs => HPBinOp s _ _ (TypedExpr_ind lhs) (TypedExpr_ind rhs)
      | TUnOp s arg => HPUnOp s _ (TypedExpr_ind arg)
      | TCast s arg => HPCast s _ (TypedExpr_ind arg)
      | TComp s lhs rhs => HPComp s _ _ (TypedExpr_ind lhs) (TypedExpr_ind rhs)
      | TLogic s lhs rhs => HPLogic s _ _ (TypedExpr_ind lhs) (TypedExpr_ind rhs)
      | TReduction s arg => HPReduction s _ (TypedExpr_ind arg)
      | TShift s lhs rhs => HPShift s _ _ (TypedExpr_ind lhs) (TypedExpr_ind rhs)
      | TAssign s lval arg => HPAssign s lval _ (TypedExpr_ind arg)
      | TShiftAssign s lval arg => HPShiftAssign s lval _ (TypedExpr_ind arg)
      | TCond s arg lhs rhs =>
          HPCond s _ _ _ (TypedExpr_ind arg) (TypedExpr_ind lhs) (TypedExpr_ind rhs)
      | TConcat s args => HPConcat s args
                           ((list_ind _ HNil
                               (fun hd tl => HCons _ tl (TypedExpr_ind hd)))
                              args)
      | TRepl s n arg => HPRepl s n _ (TypedExpr_ind arg)
      end
    .
  End TypedExpr_ind.

  Definition size e :=
    match e with
    | TAtom s _ => s
    | TBinOp s _ _ => s
    | TUnOp s _ => s
    | TCast s _ => s
    | TComp s _ _ => s
    | TLogic s _ _ => s
    | TReduction s _ => s
    | TShift s _ _ => s
    | TAssign s _ _ => s
    | TShiftAssign s _ _ => s
    | TCond s _ _ _ => s
    | TConcat s  _ => s
    | TRepl s _ _ => s
    end
  .

End TypedExpr.

