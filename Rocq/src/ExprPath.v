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
      IsPath lhs p -> IsPath (EBinOp lhs rhs) (0 :: p)
  | P_RhsBinOp : forall lhs rhs p,
      IsPath rhs p -> IsPath (EBinOp lhs rhs) (1 :: p)
  | P_UnOpArg : forall arg p,
      IsPath arg p -> IsPath (EUnOp arg) (0 :: p)
  | P_CastArg : forall arg p,
      IsPath arg p -> IsPath (ECast arg) (0 :: p)
  | P_LhsCompOp : forall lhs rhs p,
      IsPath lhs p -> IsPath (EComp lhs rhs) (0 :: p)
  | P_RhsCompOp : forall lhs rhs p,
      IsPath rhs p -> IsPath (EComp lhs rhs) (1 :: p)
  | P_LhsLogic : forall lhs rhs p,
      IsPath lhs p -> IsPath (ELogic lhs rhs) (0 :: p)
  | P_RhsLogic : forall lhs rhs p,
      IsPath rhs p -> IsPath (ELogic lhs rhs) (1 :: p)
  | P_RedArg : forall arg p,
      IsPath arg p -> IsPath (EReduction arg) (0 :: p)
  | P_LhsShift : forall lhs rhs p,
      IsPath lhs p -> IsPath (EShift lhs rhs) (0 :: p)
  | P_RhsShift : forall lhs rhs p,
      IsPath rhs p -> IsPath (EShift lhs rhs) (1 :: p)
  | P_AssignArg : forall op arg p,
      IsPath arg p -> IsPath (EAssign op arg) (0 :: p)
  | P_ShiftAssignArg : forall op arg p,
      IsPath arg p -> IsPath (EShiftAssign op arg) (0 :: p)
  | P_CondCond : forall cond tb fb p,
      IsPath cond p -> IsPath (ECond cond tb fb) (0 :: p)
  | P_CondTrue : forall cond tb fb p,
      IsPath tb p -> IsPath (ECond cond tb fb) (1 :: p)
  | P_CondFalse : forall cond tb fb p,
      IsPath fb p -> IsPath (ECond cond tb fb) (2 :: p)
  | P_ConcatArgs : forall n args e p,
      nth_error args n = Some e -> IsPath e p -> IsPath (EConcat args) (n :: p)
  | P_ReplArg : forall i arg p,
      IsPath arg p -> IsPath (ERepl i arg) (0 :: p)
  .

  Fixpoint sub_expr (e: Expr) (p: path) :=
    match e, p with
    | e, [] => Some e
    | EBinOp lhs _, 0 :: p => sub_expr lhs p
    | EBinOp _ rhs, 1 :: p => sub_expr rhs p
    | EUnOp arg, 0 :: p => sub_expr arg p
    | ECast arg, 0 :: p => sub_expr arg p
    | EComp lhs _, 0 :: p => sub_expr lhs p
    | EComp _ rhs, 1 :: p => sub_expr rhs p
    | ELogic lhs _, 0 :: p => sub_expr lhs p
    | ELogic _ rhs, 1 :: p => sub_expr rhs p
    | EReduction arg, 0 :: p => sub_expr arg p
    | EShift lhs _, 0 :: p => sub_expr lhs p
    | EShift _ rhs, 1 :: p => sub_expr rhs p
    | EAssign _ arg, 0 :: p => sub_expr arg p
    | EShiftAssign _ arg, 0 :: p => sub_expr arg p
    | ECond cond _ _, 0 :: p => sub_expr cond p
    | ECond _ tb _, 1 :: p => sub_expr tb p
    | ECond _ _ fb, 2 :: p => sub_expr fb p
    | EConcat args, i :: p =>
        match nth_error args i with
        | Some e => sub_expr e p
        | None => None
        end
    | ERepl _ arg, 0 :: p => sub_expr arg p
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
      try (destruct p as [|[|[|[]]]]; simpl in *;
           (constructor; firstorder) || congruence).
    - destruct p.
      + constructor.
      + destruct (nth_error args n) eqn:H1; simpl in H0; rewrite H1 in H0.
        * apply (P_ConcatArgs _ _ _ _ H1 (H _ _ H1 _ _ H0)).
        * congruence.
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
    - destruct H as [f [H1 H2]]. destruct e; simpl in *;
        try congruence; try (destruct (nth_error _ a)); destruct a as [|[|[]]];
        congruence || (apply IHp; eexists; intuition; eassumption).
    - destruct e; simpl in *;
        try congruence; try (destruct (nth_error _ a));
        destruct a as [|[|[]]]; congruence || apply IHp; assumption.
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
