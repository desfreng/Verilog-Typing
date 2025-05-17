From Stdlib Require Import Lists.List.

From Verilog Require Import Expr.
From Verilog Require Export Path.
From Verilog Require Import Utils.

Import ListNotations.

Import Expr.
Import Path.
Import Utils.

Module ExprPath.
  Inductive IsPath : Expr -> path -> Prop :=
  | P_Empty : forall e,
      IsPath e []
  | P_LhsBinOp : forall lhs rhs p,
      IsPath lhs p -> IsPath (EBinOp lhs rhs) (Left :: p)
  | P_RhsBinOp : forall lhs rhs p,
      IsPath rhs p -> IsPath (EBinOp lhs rhs) (Right :: p)
  | P_UnOpArg : forall arg p,
      IsPath arg p -> IsPath (EUnOp arg) (Arg :: p)
  | P_CastArg : forall arg p,
      IsPath arg p -> IsPath (ECast arg) (Arg :: p)
  | P_LhsCompOp : forall lhs rhs p,
      IsPath lhs p -> IsPath (EComp lhs rhs) (Left :: p)
  | P_RhsCompOp : forall lhs rhs p,
      IsPath rhs p -> IsPath (EComp lhs rhs) (Right :: p)
  | P_LhsLogic : forall lhs rhs p,
      IsPath lhs p -> IsPath (ELogic lhs rhs) (Left :: p)
  | P_RhsLogic : forall lhs rhs p,
      IsPath rhs p -> IsPath (ELogic lhs rhs) (Right :: p)
  | P_RedArg : forall arg p,
      IsPath arg p -> IsPath (EReduction arg) (Arg :: p)
  | P_LhsShift : forall lhs rhs p,
      IsPath lhs p -> IsPath (EShift lhs rhs) (Left :: p)
  | P_RhsShift : forall lhs rhs p,
      IsPath rhs p -> IsPath (EShift lhs rhs) (Right :: p)
  | P_AssignArg : forall op arg p,
      IsPath arg p -> IsPath (EAssign op arg) (Arg :: p)
  | P_ShiftAssignArg : forall op arg p,
      IsPath arg p -> IsPath (EShiftAssign op arg) (Arg :: p)
  | P_CondCond : forall cond tb fb p,
      IsPath cond p -> IsPath (ECond cond tb fb) (Arg :: p)
  | P_CondTrue : forall cond tb fb p,
      IsPath tb p -> IsPath (ECond cond tb fb) (Left :: p)
  | P_CondFalse : forall cond tb fb p,
      IsPath fb p -> IsPath (ECond cond tb fb) (Right :: p)
  | P_ConcatArgs : forall n args e p,
      nth_error args n = Some e -> IsPath e p -> IsPath (EConcat args) (Args n :: p)
  | P_ReplArg : forall i arg p,
      IsPath arg p -> IsPath (ERepl i arg) (Arg :: p)
  .

  Fixpoint sub_expr (e: Expr) (p: path) :=
    match e, p with
    | e, [] => Some e
    | EBinOp lhs _, Left :: p => sub_expr lhs p
    | EBinOp _ rhs, Right :: p => sub_expr rhs p
    | EUnOp arg, Arg :: p => sub_expr arg p
    | ECast arg, Arg :: p => sub_expr arg p
    | EComp lhs _, Left :: p => sub_expr lhs p
    | EComp _ rhs, Right :: p => sub_expr rhs p
    | ELogic lhs _, Left :: p => sub_expr lhs p
    | ELogic _ rhs, Right :: p => sub_expr rhs p
    | EReduction arg, Arg :: p => sub_expr arg p
    | EShift lhs _, Left :: p => sub_expr lhs p
    | EShift _ rhs, Right :: p => sub_expr rhs p
    | EAssign _ arg, Arg :: p => sub_expr arg p
    | EShiftAssign _ arg, Arg :: p => sub_expr arg p
    | ECond cond _ _, Arg :: p => sub_expr cond p
    | ECond _ tb _, Left :: p => sub_expr tb p
    | ECond _ _ fb, Right :: p => sub_expr fb p
    | EConcat args, Args i :: p =>
        match nth_error args i with
        | Some e => sub_expr e p
        | None => None
        end
    | ERepl _ arg, Arg :: p => sub_expr arg p
    | _, _ :: _ => None
    end
  .

  Notation "e @[ p ]" := (sub_expr e p) (at level 20).

  Lemma IsPath_is_sub_expr: forall e p, IsPath e p -> exists e0, e @[p] = Some e0.
  Proof.
    intros. induction H; try (destruct IHIsPath as [x H1]; exists x; assumption).
    - exists e; destruct e; reflexivity.
    - destruct IHIsPath as [x H1]; exists x. simpl. rewrite H. assumption.
  Qed.

  Lemma sub_expr_valid: forall e p f, e @[p] = Some f -> IsPath e p.
  Proof.
    induction e using Expr_ind; intros;
      try (destruct p as [|[]]; try (discriminate H); constructor; firstorder).
      - destruct p as [|[]]; try (discriminate H); try (discriminate H0).
        + constructor.
        + simpl in H0. destruct (nth_error args i) eqn:H1; try (discriminate H0).
          econstructor. eassumption. apply (H _ _ H1 _ _ H0).
  Qed.

  Lemma IsPath_sub_expr_iff: forall e p, IsPath e p <-> exists e0, e @[p] = Some e0.
  Proof.
    split.
    - apply IsPath_is_sub_expr.
    - intros [? H]. apply (sub_expr_valid _ _ _ H).
  Qed.

  Lemma sub_expr_nil: forall e, e @[[]] = Some e.
  Proof.
    intros. destruct e; reflexivity.
  Qed.

  Lemma sub_expr_chunk : forall p q e g,
      (exists f, e @[p] = Some f /\ f @[q] = Some g) <-> e @[p ++ q] = Some g.
  Proof.
    induction p; split; intros.
    - destruct H as [f [H1 H2]]. rewrite sub_expr_nil in H1. inv H1. assumption.
    - exists e. split. apply sub_expr_nil. assumption.
    - destruct H as [f [H1 H2]]. destruct e; simpl; try (discriminate H1);
        destruct a; simpl in *; try (destruct (nth_error _ i));
        (apply IHp; exists f; intuition) || discriminate H1.
    - destruct a; simpl in H;
        try (destruct e; discriminate H || (apply IHp in H; assumption));
        destruct e; discriminate H || (destruct (nth_error _ i) eqn:H';
        discriminate H || (apply IHp in H; simpl; rewrite H'; assumption)).
  Qed.

  Lemma IsPath_chunk : forall e p c,
      IsPath e (p ++ c) <-> (exists f, e @[p] = Some f /\ IsPath f c).
  Proof.
    split; intros.
    - destruct (IsPath_is_sub_expr _ _ H) as [g H1]. apply sub_expr_chunk in H1.
      destruct H1 as [f [H2 H3]]. exists f. split. assumption. apply IsPath_sub_expr_iff.
      exists g. assumption.
    - destruct H as [f [H1 H2]]. apply IsPath_sub_expr_iff.
      apply IsPath_sub_expr_iff in H2. destruct H2 as [g H2]. exists g.
      apply sub_expr_chunk. exists f. intuition.
  Qed.

  Theorem IsPath_dec : forall e p, {IsPath e p} + {~(IsPath e p)}.
  Proof.
    intros. destruct (e @[p]) eqn:Hep.
    - left. apply (sub_expr_valid _ _ _ Hep).
    - right. unfold not. intros. rewrite IsPath_sub_expr_iff in H. destruct H.
      congruence.
  Qed.
End ExprPath.
