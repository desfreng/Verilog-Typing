From Stdlib Require Import Lists.List.

From Verilog Require Import TypedExpr.
From Verilog Require Export Path.
From Verilog Require Import Utils.

Import ListNotations.

Import TypedExpr.
Import Path.
Import Utils.

Module TypedExprPath.
  Inductive IsTypedPath : TypedExpr -> path -> Prop :=
  | TP_Empty : forall e,
      IsTypedPath e []
  | TP_LhsBinOp : forall s lhs rhs p,
      IsTypedPath lhs p -> IsTypedPath (TBinOp s lhs rhs) (Left :: p)
  | TP_RhsBinOp : forall s lhs rhs p,
      IsTypedPath rhs p -> IsTypedPath (TBinOp s lhs rhs) (Right :: p)
  | TP_UnOpArg : forall s arg p,
      IsTypedPath arg p -> IsTypedPath (TUnOp s arg) (Arg :: p)
  | TP_CastArg : forall s arg p,
      IsTypedPath arg p -> IsTypedPath (TCast s arg) (Arg :: p)
  | TP_LhsCompOp : forall s lhs rhs p,
      IsTypedPath lhs p -> IsTypedPath (TComp s lhs rhs) (Left :: p)
  | TP_RhsCompOp : forall s lhs rhs p,
      IsTypedPath rhs p -> IsTypedPath (TComp s lhs rhs) (Right :: p)
  | TP_LhsLogic : forall s lhs rhs p,
      IsTypedPath lhs p -> IsTypedPath (TLogic s lhs rhs) (Left :: p)
  | TP_RhsLogic : forall s lhs rhs p,
      IsTypedPath rhs p -> IsTypedPath (TLogic s lhs rhs) (Right :: p)
  | TP_RedArg : forall s arg p,
      IsTypedPath arg p -> IsTypedPath (TReduction s arg) (Arg :: p)
  | TP_LhsShift : forall s lhs rhs p,
      IsTypedPath lhs p -> IsTypedPath (TShift s lhs rhs) (Left :: p)
  | TP_RhsShift : forall s lhs rhs p,
      IsTypedPath rhs p -> IsTypedPath (TShift s lhs rhs) (Right :: p)
  | TP_AssignArg : forall s op arg p,
      IsTypedPath arg p -> IsTypedPath (TAssign s op arg) (Arg :: p)
  | TP_ShiftAssignArg : forall s op arg p,
      IsTypedPath arg p -> IsTypedPath (TShiftAssign s op arg) (Arg :: p)
  | TP_CondCond : forall s cond tb fb p,
      IsTypedPath cond p -> IsTypedPath (TCond s cond tb fb) (Arg :: p)
  | TP_CondTrue : forall s cond tb fb p,
      IsTypedPath tb p -> IsTypedPath (TCond s cond tb fb) (Left :: p)
  | TP_CondFalse : forall s cond tb fb p,
      IsTypedPath fb p -> IsTypedPath (TCond s cond tb fb) (Right :: p)
  | TP_ConcatArgs : forall s n args e p,
      nth_error args n = Some e -> IsTypedPath e p ->
      IsTypedPath (TConcat s args) (Args n :: p)
  | TP_ReplArg : forall s i arg p,
      IsTypedPath arg p -> IsTypedPath (TRepl s i arg) (Arg :: p)
  .

  Fixpoint sub_typed_expr (e: TypedExpr) (p: path) :=
    match e, p with
    | e, [] => Some e
    | TBinOp _ lhs _, Left :: p => sub_typed_expr lhs p
    | TBinOp _ _ rhs, Right :: p => sub_typed_expr rhs p
    | TUnOp _ arg, Arg :: p => sub_typed_expr arg p
    | TCast _ arg, Arg :: p => sub_typed_expr arg p
    | TComp _ lhs _, Left :: p => sub_typed_expr lhs p
    | TComp _ _ rhs, Right :: p => sub_typed_expr rhs p
    | TLogic _ lhs _, Left :: p => sub_typed_expr lhs p
    | TLogic _ _ rhs, Right :: p => sub_typed_expr rhs p
    | TReduction _ arg, Arg :: p => sub_typed_expr arg p
    | TShift _ lhs _, Left :: p => sub_typed_expr lhs p
    | TShift _ _ rhs, Right :: p => sub_typed_expr rhs p
    | TAssign _ _ arg, Arg :: p => sub_typed_expr arg p
    | TShiftAssign _ _ arg, Arg :: p => sub_typed_expr arg p
    | TCond _ cond _ _, Arg :: p => sub_typed_expr cond p
    | TCond _ _ tb _, Left :: p => sub_typed_expr tb p
    | TCond _ _ _ fb, Right :: p => sub_typed_expr fb p
    | TConcat _ args, Args i :: p =>
        match nth_error args i with
        | Some e => sub_typed_expr e p
        | None => None
        end
    | TRepl _ _ arg, Arg :: p => sub_typed_expr arg p
    | _, _ :: _ => None
    end
  .

  Notation "e @@[ p ]" := (sub_typed_expr e p) (at level 20).

  Lemma IsTypedPath_is_sub_typed_expr: forall e p, IsTypedPath e p -> exists e0, e @@[p] = Some e0.
  Proof.
    intros. induction H; try (destruct IHIsTypedPath as [x H1]; exists x; assumption).
    - exists e; destruct e; reflexivity.
    - destruct IHIsTypedPath as [x H1]; exists x. simpl. rewrite H. assumption.
  Qed.

  Lemma sub_typed_expr_valid: forall e p f, e @@[p] = Some f -> IsTypedPath e p.
  Proof.
    induction e using TypedExpr_ind; intros;
      try (destruct p as [|[]]; try (discriminate H); constructor; firstorder).
      - destruct p as [|[]]; try (discriminate H); try (discriminate H0).
        + constructor.
        + simpl in H0. destruct (nth_error args i) eqn:H1; try (discriminate H0).
          econstructor. eassumption. apply (H _ _ H1 _ _ H0).
  Qed.

  Lemma IsTypedPath_sub_typed_expr_iff: forall e p, IsTypedPath e p <-> exists e0, e @@[p] = Some e0.
  Proof.
    split.
    - apply IsTypedPath_is_sub_typed_expr.
    - intros [? H]. apply (sub_typed_expr_valid _ _ _ H).
  Qed.

  Lemma sub_typed_expr_nil: forall e, e @@[ [] ] = Some e.
  Proof.
    intros. destruct e; reflexivity.
  Qed.

  Lemma sub_exp_chunk : forall p q e g,
      (exists f, e @@[p] = Some f /\ f @@[q] = Some g) <-> e @@[p ++ q] = Some g.
  Proof.
    induction p; split; intros.
    - destruct H as [f [H1 H2]]. rewrite sub_typed_expr_nil in H1. inv H1. assumption.
    - exists e. split. apply sub_typed_expr_nil. assumption.
    - destruct H as [f [H1 H2]]. destruct e; simpl; try (discriminate H1);
        destruct a; simpl in *; try (destruct (nth_error _ i));
        (apply IHp; exists f; intuition) || discriminate H1.
    - destruct a; simpl in H;
        try (destruct e; discriminate H || (apply IHp in H; assumption));
        destruct e; discriminate H || (destruct (nth_error _ i) eqn:H';
        discriminate H || (apply IHp in H; simpl; rewrite H'; assumption)).
  Qed.

  Lemma IsTypedPath_chunk : forall e p c,
      IsTypedPath e (p ++ c) <-> (exists f, e @@[p] = Some f /\ IsTypedPath f c).
  Proof.
    split; intros.
    - destruct (IsTypedPath_is_sub_typed_expr _ _ H) as [g H1].
      apply sub_exp_chunk in H1. destruct H1 as [f [H2 H3]].
      exists f. split. assumption. apply IsTypedPath_sub_typed_expr_iff.
      exists g. assumption.
    - destruct H as [f [H1 H2]]. apply IsTypedPath_sub_typed_expr_iff.
      apply IsTypedPath_sub_typed_expr_iff in H2. destruct H2 as [g H2]. exists g.
      apply sub_exp_chunk. exists f. intuition.
  Qed.

End TypedExprPath.
