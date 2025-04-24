From Stdlib Require Import Lists.List.
From Verilog Require Import Expr.
From Verilog Require Import Path.
From Verilog Require Import Utils.

Import ListNotations.
Import Expr.
Import Path.
Import Utils.

Import Notation.

Set Implicit Arguments.

Definition push {X: Type} l (x: X) := l ++ [x].

Fixpoint e_ctx (e: Expr) (p: path) : list path :=
  match e with
  | EAtom _ => []
  | EBinOp lhs rhs => e_ctx lhs (push p Lhs) ++ e_ctx rhs (push p Rhs)
  | EUnOp arg => e_ctx arg (push p Arg)
  | ECast arg => let p' := push p Arg in p' :: e_ctx arg p'
  | EComp lhs rhs => p :: e_ctx lhs (push p Lhs) ++ e_ctx rhs (push p Rhs)
  | ELogic lhs rhs =>
      let lhsP := push p Lhs in
      let rhsP := push p Rhs in
      lhsP :: e_ctx lhs lhsP ++ rhsP :: e_ctx rhs rhsP
  | EReduction arg => let p' := push p Arg in p' :: e_ctx arg p'
  | EShift lhs rhs =>
      let rhsP := push p Rhs in
      e_ctx lhs (push p Lhs) ++ rhsP :: e_ctx rhs rhsP
  | EAssign _ arg => let p' := push p Arg in p' :: e_ctx arg p'
  | EShiftAssign _ arg => let p' := push p Arg in p' :: e_ctx arg p'
  | ECond cond tb fb =>
      let condP := push p Cond in
      condP :: e_ctx cond condP ++ e_ctx tb (push p Lhs)
        ++ e_ctx fb (push p Rhs)
  | EConcat args =>
      concat (mapI (fun i e => let newP := push p (Args i) in newP :: e_ctx e newP) args)
  | ERepl _ arg => let p' := push p Arg in p' :: e_ctx arg p'
  | EInside arg args =>
      concat (mapI (fun i e => let newP := push p (Args i) in newP :: e_ctx e newP) args)
  end
.

Definition contexts (e: Expr) := [] :: e_ctx e [].

Lemma e_ctx_comp: forall e p c, In c (e_ctx e p) -> exists l, c = p ++ l /\ IsPath e l.
Proof.
  Ltac _e_ctx_comp_tac :=
    match goal with
    | [ H: ex _ |- ex _ ] =>
        destruct H as [? [H1 H2]]; subst; eexists; split;
        [ rewrite <- app_assoc; reflexivity | constructor; assumption]
    | [ IHe: _, H : In _ (e_ctx _ _) |- _ ] =>
        apply IHe in H; _e_ctx_comp_tac
    | [ H : In _ (_ :: e_ctx _ _) |- _ ] =>
        apply in_inv in H; destruct H; subst; _e_ctx_comp_tac
    | [ H: _, Hi: In _ (concat _) |- _ ] =>
        apply in_concat in Hi; destruct Hi as [x [Ht H2]]; apply mapI_values in Ht;
        destruct Ht as [n [x0 [H1 H3]]]; subst; apply in_inv in H2; destruct H2; subst;
        [ exists [Args n]; split; [reflexivity | econstructor; [apply H1 | constructor]]
        | destruct (H _ _ H1 _ _ Hi) as [? [H2 H3]]; subst; eexists; split;
          [rewrite <- app_assoc; reflexivity | econstructor; [apply H1 | assumption]]]
    | [ _ : _ |- ex (fun _ => _ ++ [?x] = _ /\ _) ] =>
        exists [x]; split; [reflexivity | constructor; constructor]
    end
  .
  induction e using Expr_ind; intros; simpl in *; unfold push in *;
    repeat (rewrite in_app_iff in *; destruct H as [H|H]); intuition; subst;
    try _e_ctx_comp_tac.
  - exists []. rewrite app_nil_r. split. reflexivity. constructor.
Qed.


Lemma e_ctx_prefix: forall e p c, In (p ++ c) (e_ctx e p) <-> In c (e_ctx e []).
Proof.
  Ltac _e_ctx_pre_tac_internal :=
    match goal with
    | [ IHe: _, _: In (_ ++ _) _ |- _ ] =>
        rewrite app_assoc in *; rewrite IHe in *; intuition
    end
  .
  Ltac _e_ctx_pre_tac :=
    match goal with
    | [ H: In _ (e_ctx _ [_]) |- _ ] =>
        destruct (e_ctx_comp _ _ _ H) as [? [? _]]; subst; _e_ctx_pre_tac_internal
    | [ H: In _ (e_ctx _ (_ ++ _)) |- _ ] =>
        destruct (e_ctx_comp _ _ _ H) as [? [?He _]]; rewrite <- app_assoc in He;
        apply app_inv_head in He; subst; _e_ctx_pre_tac_internal
    | [ H: ?x ++ _ = ?x ++ _ |- _ ] => apply app_inv_head in H; subst; intuition
    end
  .
  induction e using Expr_ind;
    intros; simpl in *; unfold push in *; repeat (rewrite in_app_iff); simpl in *;
    split; intros H0; intuition; try _e_ctx_pre_tac; subst; auto.
  - left. apply (app_inv_head p). rewrite app_nil_r. assumption.
  - left. symmetry. apply app_nil_r.
  - rewrite in_concat in *. destruct H0 as [x [H1 H2]]. rewrite mapI_values in H1.
    destruct H1 as [n [e [H1 H3]]]. subst. simpl in H2. destruct H2; eexists;
      rewrite mapI_values; split; try (exists n; exists e; split; [apply H1 | reflexivity]).
    + left. apply (app_inv_head p). assumption.
    + right. _e_ctx_pre_tac. apply H1. apply H1.
  - rewrite in_concat in *. destruct H0 as [x [H1 H2]]. rewrite mapI_values in H1.
    destruct H1 as [n [e [H1 H3]]]. subst. simpl in H2. destruct H2; eexists;
      rewrite mapI_values; split; try (exists n; exists e; split; [apply H1 | reflexivity]).
    + subst. left. reflexivity.
    + right. _e_ctx_pre_tac. apply H1. apply H1.
  - rewrite in_concat in *. destruct H0 as [x [H1 H2]]. rewrite mapI_values in H1.
    destruct H1 as [n [f [H1 H3]]]. subst. simpl in H2. destruct H2; eexists;
      rewrite mapI_values; split; try (exists n; exists f; split; [apply H1 | reflexivity]).
    + left. apply (app_inv_head p). assumption.
    + right. _e_ctx_pre_tac. apply H1. apply H1.
  - rewrite in_concat in *. destruct H0 as [x [H1 H2]]. rewrite mapI_values in H1.
    destruct H1 as [n [f [H1 H3]]]. subst. simpl in H2. destruct H2; eexists;
      rewrite mapI_values; split; try (exists n; exists f; split; [apply H1 | reflexivity]).
    + subst. left. reflexivity.
    + right. _e_ctx_pre_tac. apply H1. apply H1.
Qed.

Lemma e_ctx_is_path: forall e e0 p c,
    sub_expr e p = Some e0 -> In c (e_ctx e0 p) -> IsPath e c.
Proof.
  intros e e0 p c H1 H2.
  assert (H3: exists l, c = p ++ l /\ IsPath e0 l). apply (e_ctx_comp _ _ _ H2).
  destruct H3 as [l [H3 H4]]. subst.
  apply IsPath_chunk. exists e0. intuition.
Qed.


Lemma contexts_is_path: forall e c, In c (contexts e) -> IsPath e c.
Proof.
  intros. unfold contexts in H. simpl in H. destruct H.
  - subst. constructor.
  - apply (e_ctx_is_path _ _ _ (sub_exp_nil e) H).
Qed.

