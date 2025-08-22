From Stdlib Require Import Lists.List.

From Verilog Require Import TaggedExpr.
From Verilog Require Export Path.
From Verilog Require Import Utils.

Import ListNotations.

Import TaggedExpr.
Import Path.
Import Utils.

Module TaggedExprPath.
  Inductive IsTypedPath {T: Type} : TaggedExpr T -> path -> Prop :=
  | TP_Empty : forall e,
      IsTypedPath e []
  | TP_LhsBinOp : forall tag lhs rhs p,
      IsTypedPath lhs p ->
      IsTypedPath (TExpr (TBinOp lhs rhs) tag) (0 :: p)
  | TP_RhsBinOp : forall tag lhs rhs p,
      IsTypedPath rhs p ->
      IsTypedPath (TExpr (TBinOp lhs rhs) tag) (1 :: p)
  | TP_UnOpArg : forall tag arg p,
      IsTypedPath arg p ->
      IsTypedPath (TExpr (TUnOp arg) tag) (0 :: p)
  | TP_LhsCompOp : forall tag lhs rhs p,
      IsTypedPath lhs p ->
      IsTypedPath (TExpr (TComp lhs rhs) tag) (0 :: p)
  | TP_RhsCompOp : forall tag lhs rhs p,
      IsTypedPath rhs p ->
      IsTypedPath (TExpr (TComp lhs rhs) tag) (1 :: p)
  | TP_LhsLogic : forall tag lhs rhs p,
      IsTypedPath lhs p ->
      IsTypedPath (TExpr (TLogic lhs rhs) tag) (0 :: p)
  | TP_RhsLogic : forall tag lhs rhs p,
      IsTypedPath rhs p ->
      IsTypedPath (TExpr (TLogic lhs rhs) tag) (1 :: p)
  | TP_RedArg : forall tag arg p,
      IsTypedPath arg p ->
      IsTypedPath (TExpr (TReduction arg) tag) (0 :: p)
  | TP_LhsShift : forall tag lhs rhs p,
      IsTypedPath lhs p ->
      IsTypedPath (TExpr (TShift lhs rhs) tag) (0 :: p)
  | TP_RhsShift : forall tag lhs rhs p,
      IsTypedPath rhs p ->
      IsTypedPath (TExpr (TShift lhs rhs) tag) (1 :: p)
  | TP_AssignArg : forall tag op arg p,
      IsTypedPath arg p ->
      IsTypedPath (TExpr (TAssign op arg) tag) (0 :: p)
  | TP_CondCond : forall tag cond tb fb p,
      IsTypedPath cond p ->
      IsTypedPath (TExpr (TCond cond tb fb) tag) (0 :: p)
  | TP_CondTrue : forall tag cond tb fb p,
      IsTypedPath tb p ->
      IsTypedPath (TExpr (TCond cond tb fb) tag) (1 :: p)
  | TP_CondFalse : forall tag cond tb fb p,
      IsTypedPath fb p ->
      IsTypedPath (TExpr (TCond cond tb fb) tag) (2 :: p)
  | TP_ConcatArgs : forall tag n args e p,
      nth_error args n = Some e -> IsTypedPath e p ->
      IsTypedPath (TExpr (TConcat args) tag) (n :: p)
  | TP_ReplArg : forall tag i arg p,
      IsTypedPath arg p ->
      IsTypedPath (TExpr (TRepl i arg) tag) (0 :: p)
  .

  Fixpoint sub_typed_expr {T: Type} (e: TaggedExpr T) (p: path) :=
    match e, p with
    | e, [] => Some e
    | TExpr (TBinOp lhs _) _, 0 :: p => sub_typed_expr lhs p
    | TExpr (TBinOp _ rhs) _, 1 :: p => sub_typed_expr rhs p
    | TExpr (TUnOp arg) _, 0 :: p => sub_typed_expr arg p
    | TExpr (TComp lhs _) _, 0 :: p => sub_typed_expr lhs p
    | TExpr (TComp _ rhs) _, 1 :: p => sub_typed_expr rhs p
    | TExpr (TLogic lhs _) _, 0 :: p => sub_typed_expr lhs p
    | TExpr (TLogic _ rhs) _, 1 :: p => sub_typed_expr rhs p
    | TExpr (TReduction arg) _, 0 :: p => sub_typed_expr arg p
    | TExpr (TShift lhs _) _, 0 :: p => sub_typed_expr lhs p
    | TExpr (TShift _ rhs) _, 1 :: p => sub_typed_expr rhs p
    | TExpr (TAssign _ arg) _, 0 :: p => sub_typed_expr arg p
    | TExpr (TCond cond _ _) _, 0 :: p => sub_typed_expr cond p
    | TExpr (TCond _ tb _) _, 1 :: p => sub_typed_expr tb p
    | TExpr (TCond _ _ fb) _, 2 :: p => sub_typed_expr fb p
    | TExpr (TConcat args) _, i :: p =>
        match nth_error args i with
        | Some e => sub_typed_expr e p
        | None => None
        end
    | TExpr (TRepl _ arg) _, 0 :: p => sub_typed_expr arg p
    | TExpr _ _, _ :: _ => None
    end
  .

  Notation "e @@[ p ]" := (sub_typed_expr e p) (at level 20).

  Lemma sub_typed_expr_nil: forall T (e: TaggedExpr T), e @@[[]] = Some e.
  Proof.
    intros. destruct e as [[]]; reflexivity.
  Qed.

  Lemma IsTypedPath_is_sub_typed_expr: forall T (e: TaggedExpr T) p,
      IsTypedPath e p -> exists e0, e @@[p] = Some e0.
  Proof.
    intros. induction H; try (destruct IHIsTypedPath as [x H1]; exists x; assumption).
    - exists e. apply sub_typed_expr_nil.
    - destruct IHIsTypedPath as [x H1]; exists x. simpl. rewrite H. assumption.
  Qed.

  Lemma sub_typed_expr_valid: forall T (e: TaggedExpr T) p f,
      e @@[p] = Some f -> IsTypedPath e p.
  Proof.
    induction e using TaggedExpr_ind; intros;
      try (destruct p as [|[|[|[]]]]; simpl in *;
           (constructor; firstorder) || congruence).
    - destruct p.
      + constructor.
      + destruct (nth_error args n) eqn:H1; simpl in H0; rewrite H1 in H0.
        * apply (TP_ConcatArgs _ _ _ _ _ H1 (H _ _ H1 _ _ H0)).
        * congruence.
  Qed.

  Lemma IsTypedPath_sub_typed_expr_iff:
    forall T (e: TaggedExpr T) p, IsTypedPath e p <-> exists e0, e @@[p] = Some e0.
  Proof.
    split.
    - apply IsTypedPath_is_sub_typed_expr.
    - intros [? H]. apply (sub_typed_expr_valid _ _ _ _ H).
  Qed.

  Lemma sub_typed_expr_chunk : forall T p q (e: TaggedExpr T) g,
      (exists f, e @@[p] = Some f /\ f @@[q] = Some g) <-> e @@[p ++ q] = Some g.
  Proof.
    induction p; split; intros.
    - destruct H as [f [H1 H2]]. rewrite sub_typed_expr_nil in H1. inv H1. assumption.
    - exists e. split. apply sub_typed_expr_nil. assumption.
    - destruct H as [f [H1 H2]]. destruct e as [[]]; simpl in *;
        try congruence; try (destruct (nth_error _ a)); destruct a as [|[|[]]];
        congruence || (apply IHp; eexists; intuition; eassumption).
    - destruct e as [[]]; simpl in *;
        try congruence; try (destruct (nth_error _ a));
        destruct a as [|[|[]]]; congruence || apply IHp; assumption.
  Qed.

  Lemma IsTypedPath_chunk : forall T (e: TaggedExpr T) p c,
      IsTypedPath e (p ++ c) <-> (exists f, e @@[p] = Some f /\ IsTypedPath f c).
  Proof.
    split; intros.
    - destruct (IsTypedPath_is_sub_typed_expr _ _ _ H) as [g H1].
      apply sub_typed_expr_chunk in H1.
      destruct H1 as [f [H2 H3]]. exists f. split. assumption.
      apply IsTypedPath_sub_typed_expr_iff.
      exists g. assumption.
    - destruct H as [f [H1 H2]]. apply IsTypedPath_sub_typed_expr_iff.
      apply IsTypedPath_sub_typed_expr_iff in H2. destruct H2 as [g H2]. exists g.
      apply sub_typed_expr_chunk. exists f. intuition.
  Qed.

  Theorem IsTypedPath_dec : forall T (e: TaggedExpr T) p,
      {IsTypedPath e p} + {~(IsTypedPath e p)}.
  Proof.
    intros. destruct (e @@[p]) eqn:Hep.
    - left. apply (sub_typed_expr_valid _ _ _ _ Hep).
    - right. unfold not. intros. rewrite IsTypedPath_sub_typed_expr_iff in H. destruct H.
      congruence.
  Qed.
End TaggedExprPath.
