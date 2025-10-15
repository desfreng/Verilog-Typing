From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import TaggedExpr.
From Verilog Require Import TaggedExprPath.
From Verilog Require Import TypeSystem.
From Verilog Require Import Spec.
From Verilog Require Import Equiv.
From Verilog Require Import Utils.

Import Nat.
Import ListNotations.

Import Path.
Import Expr.
Import ExprPath.
Import TaggedExpr.
Import TaggedExprPath.
Import TypeSystem.
Import Equiv.
Import Utils.
Import Learn.

Module Algo.
  Fixpoint determine e :=
    match e with
    | EOperand op => op
    | EBinOp lhs rhs =>
        let lhs_size := determine lhs in
        let rhs_size := determine rhs in
        max lhs_size rhs_size
    | EUnOp arg =>
        let arg_size := determine arg in
        arg_size
    | EComp lhs rhs => 1
    | ELogic lhs rhs => 1
    | EReduction arg => 1
    | EShift lhs rhs =>
        let lhs_size := determine lhs in
        lhs_size
    | EAssign lval_size arg => lval_size
    | ECond arg lhs rhs =>
        let lhs_size := determine lhs in
        let rhs_size := determine rhs in
        max lhs_size rhs_size
    | EConcat args =>
        let exprs_size := map determine args in
        sum exprs_size
    | ERepl n arg =>
        let arg_size := determine arg in
        n * arg_size
    end
  .

  Fixpoint propagate e target_size :=
    let annotate := TExpr in
    match e with
    | EOperand op => annotate (TOperand op) target_size
    | EBinOp lhs rhs =>
        let ann_lhs := propagate lhs target_size in
        let ann_rhs := propagate rhs target_size in
        annotate (TBinOp ann_lhs ann_rhs) target_size
    | EUnOp arg =>
        let ann_arg := propagate arg target_size in
        annotate (TUnOp ann_arg) target_size
    | EComp lhs rhs =>
        let lhs_size := determine lhs in
        let rhs_size := determine rhs in
        let arg_size := max lhs_size rhs_size in
        let ann_lhs := propagate lhs arg_size in
        let ann_rhs := propagate rhs arg_size in
        annotate (TComp ann_lhs ann_rhs) target_size
    | ELogic lhs rhs =>
        let lhs_size := determine lhs in
        let ann_lhs := propagate lhs lhs_size in
        let rhs_size := determine rhs in
        let ann_rhs := propagate rhs rhs_size in
        annotate (TLogic ann_lhs ann_rhs) target_size
    | EReduction arg =>
        let arg_size := determine arg in
        let ann_arg := propagate arg arg_size in
        annotate (TReduction ann_arg) target_size
    | EShift lhs rhs =>
        let ann_lhs := propagate lhs target_size in
        let rhs_size := determine rhs in
        let ann_rhs := propagate rhs rhs_size in
        annotate (TShift ann_lhs ann_rhs) target_size
    | EAssign lval_size rhs =>
        let rhs_size := determine rhs in
        let arg_size := max lval_size rhs_size in
        let ann_rhs := propagate rhs arg_size in
        annotate (TAssign lval_size ann_rhs) target_size
    | ECond cond true_expr false_expr =>
        let cond_size := determine cond in
        let ann_cond := propagate cond cond_size in
        let ann_true := propagate true_expr target_size in
        let ann_false := propagate false_expr target_size in
        annotate (TCond ann_cond ann_true ann_false) target_size
    | EConcat args =>
        let ann_args := map (fun expr_i => let expr_i_size := determine expr_i in
                                        propagate expr_i expr_i_size) args in
        annotate (TConcat ann_args) target_size
    | ERepl n inner_expr =>
        let inner_size := determine inner_expr in
        let ann_inner := propagate inner_expr inner_size in
        annotate (TRepl n ann_inner) target_size
    end
  .

  Definition type e :=
    let expr_size := determine e in
    propagate e expr_size.

  Definition size_at {T: Type} (e: TaggedExpr T) p := option_map tag (e @@[p]).

  Lemma propagate_shape1 : forall e p,
      IsPath e p -> forall s, IsTypedPath (propagate e s) p.
  Proof.
    intros. generalize dependent s. induction H; intros; simpl in *;
      econstructor; firstorder.
      rewrite nth_error_map. rewrite H. reflexivity.
  Qed.

  Lemma propagate_shape2 : forall e p s, IsTypedPath (propagate e s) p -> IsPath e p.
  Proof.
    induction e; intros; try (inv H; constructor; firstorder).
    inv H0. constructor. destruct (nth_error args n) eqn:Hnth;
      rewrite nth_error_map in H3; rewrite Hnth in H3; inv H3.
    econstructor. eassumption. apply (H _ _ Hnth _ _ H5).
  Qed.

  Theorem propagate_shape : forall e p, IsPath e p <-> forall s, IsTypedPath (propagate e s) p.
  Proof.
    split; intros.
    - apply (propagate_shape1 _ _ H).
    - apply (propagate_shape2 _ _ 0 (H _)).
  Qed.

  Theorem type_shape : forall e p, IsPath e p <-> IsTypedPath (type e) p.
  Proof.
    split; intros; unfold type in *.
    - apply (propagate_shape1 _ _ H _).
    - apply (propagate_shape2 _ _ _ H).
  Qed.

  Lemma determine_top_size : forall e, determine e = Spec.determine e.
  Proof. induction e using Expr_ind; reflexivity. Qed.

  Lemma propagate_top_size : forall e s, tag (propagate e s) = s.
  Proof. intros; destruct e; reflexivity. Qed.

  Lemma type_top_size : forall e, tag (type e) = determine e.
  Proof.
    intros. unfold type. rewrite determine_top_size. apply propagate_top_size.
  Qed.

  Ltac inv_path :=
    match goal with
    | [ H: IsPath (_ _) _ |- _ ] => inv H
    end
  .

  Lemma propagate_size_path_lemma :
    forall e s fc, e <== s -| fc -> forall p, IsPath e p -> fc p = size_at (propagate e s) p.
  Proof.
    Ltac _propagate_size_dec :=
      match goal with
      | [ |- _ = option_map _ ((propagate _ (max ?n ?m)) @@[_]) ] =>
          let nH := fresh in destruct (max_dec_bis n m) as [[nH ?]|[nH ?]];
                             rewrite nH in *; clear nH
      end
    .
    Ltac _propagate_size_p_lem :=
      match goal with
      | [ H: _ = _ |- _ ] => rewrite <- H
      | [ H: _ -> _ |- _ ] => eapply H; eassumption
      | [ H: _ ==> _ -| _ |- _ ] =>
          learn (synth_must_be_determine _ _ _ H); splitHyp; subst
      | [ H: ?e ==> Spec.determine ?e -| _ |- _ ] =>
          learn (synth_can_check _ _ _ _ H (le_refl _)); existsHyp
      | [ H: ?e ==> ?t -| ?f1, F: ?e <== ?t -| ?f2 |- _ ] =>
          let nH := fresh in assert (nH: f1 = f2) by
            (extensionality p; apply (synth_check_inj_f _ _ _ _ H F));
                             learn nH; subst
      | [ H: ?e1 ==> ?t -| _, F: ?e2 <== ?t -| _ |- _ ] =>
          learn (synth_check_determine_order _ _ _ _ _ _ H F (le_refl _));
          try antisym; subst
      | [ H: ?e <== ?t -| _, F: ?t <= Spec.determine ?e |- _ ] =>
          learn (Equiv.synth_and_order _ _ _ H F); subst
      | [ H : context [Spec.determine _] |- _ ] => rewrite determine_top_size in H
      end
    .
    induction e using Expr_ind; intros; simpl in *; unfold size_at; inv_path;
      try (apply check_root in H; simpl; congruence);
      inv_ts; simpl; repeat (rewrite determine_top_size); try _propagate_size_dec;
      repeat _propagate_size_p_lem; try lia; try reflexivity.
    repeat (gen_nth). repeat (rewrite nth_error_map). rewrite H3. rewrite H0. simpl.
    repeat (rewrite up_top_size). specialize (H8 _ _ _ _ H3 H1 H0).
    repeat _propagate_size_p_lem.
  Qed.

  Theorem propagate_size_path : forall e s,
      determine e <= s -> e <== s -| size_at (propagate e s).
  Proof.
    intros. destruct (always_synth e) as [t [f Hs]].
    destruct (synth_must_be_determine _ _ _ Hs). subst. clear H1.
    destruct (synth_can_check _ _ _ _ Hs H) as [fc Hc]. clear Hs. clear f.
    assert (Hfc: fc = size_at (propagate e s)).
    {
      extensionality p. destruct (IsPath_dec e p).
      - apply propagate_size_path_lemma; assumption.
      - assert (fc p = None).
        { destruct (fc p) eqn:Hfc; try reflexivity. exfalso. apply n.
          rewrite (check_f_path _ _ _ Hc). firstorder. }
        assert (propagate e s @@[ p] = None).
        { destruct (propagate e s @@[ p]) eqn:Hpr; try reflexivity. exfalso.
          apply n. eapply propagate_shape2.
          apply (sub_typed_expr_valid _ _ _ _ Hpr). }
        unfold size_at. rewrite H1. assumption.
    }
    rewrite <- Hfc. assumption.
  Qed.

  Theorem type_correction: forall e, exists t, e ==> t -| size_at (type e).
  Proof.
    intros. exists (determine e). destruct (always_synth e) as [t [f Hs]].
    destruct (synth_must_be_determine _ _ _ Hs); subst.
    assert (Hc: e <== determine e -| size_at (type e)).
    { unfold type. rewrite determine_top_size. apply propagate_size_path. reflexivity. }
    assert (Hf: f = size_at (type e))
      by (extensionality p; apply (synth_check_inj_f _ _ _ _ Hs Hc)).
    subst. assumption.
  Qed.
End Algo.
