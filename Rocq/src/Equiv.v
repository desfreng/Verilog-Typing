From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.

From Verilog Require Import Expr.
From Verilog Require Import Path.
From Verilog Require Import Spec.
From Verilog Require Import TypeSystem.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.

Import Expr.
Import Path.
Import Spec.
Import TypeSystem.
Import Utils.

Set Implicit Arguments.

Module Equiv.

  Theorem spec_implies_ts : forall f1,
      propagate_def f1 -> forall e f2, e ==> (determine e) -| f2 ->
                                 forall p, IsPath e p -> forall n, f1 e p = n -> f2 p = Some n.
  Proof.
    Ltac _gen_eq_spec_ts :=
      match goal with
      | [ F: _ @[_] = Some (EBinOp _ _), H: binop_propagate _ |- _ ] =>
          destruct (H _ _ _ _ F)
      | [ F: _ @[_] = Some (EUnOp _), H: unop_propagate _ |- _ ] =>
          apply H in F
      | [ F: _ @[_] = Some (ECast _), H: cast_propagate _ |- _ ] =>
          apply H in F
      | [ F: _ @[_] = Some (EComp _ _), H: comp_propagate _ |- _ ] =>
          destruct (H _ _ _ _ F _ (eq_refl _))
      | [ F: _ @[_] = Some (ELogic _ _), H: logic_propagate _ |- _ ] =>
          destruct (H _ _ _ _ F)
      | [ F: _ @[_] = Some (EReduction _), H: red_propagate _ |- _ ] =>
          apply H in F
      | [ F: _ @[_] = Some (EShift _ _), H: shift_propagate _ |- _ ] =>
          destruct (H _ _ _ _ F)
      | [ F: _ @[_] = Some (EAssign _ _), H: assign_propagate _ |- _ ] =>
          specialize (H _ _ _ _ F _ (eq_refl _))
      | [ F: _ @[_] = Some (EShiftAssign _ _), H: shiftassign_propagate _ |- _ ] =>
          apply H in F
      | [ F: _ @[_] = Some (ECond _ _ _), H: cond_propagate _ |- _ ] =>
          destruct (H _ _ _ _ _ F) as [? [? ?]]
      | [ G: nth_error _ _ = _, F: _ @[_] = Some (EConcat _),
              H: concat_propagate _ |- _ ] =>
          specialize (H _ _ _ F _ _ G)
      | [ F: _ @[_] = Some (ERepl _ _), H: repl_propagate _ |- _ ] =>
          specialize (H _ _ _ _ F)
      end
    .
    Ltac _tac_spec_ts :=
      match goal with
      | [ H: ?x = ?n, G: _ <== ?n -| ?f |- ?f _ = Some ?x ] =>
          rewrite H; apply (check_root G)
      | [ H: ?x = ?n, G: _ ==> ?n -| ?f |- ?f _ = Some ?x ] =>
          rewrite H; apply (synth_root G)
      | [ H: ?x ==> _ -| ?f |- ?f [] = Some (determine ?x) ] =>
          destruct (synth_must_be_determine H); assumption
      end
    .
    induction p using path_ind; intros; propagate_def_split.
    - rewrite (synth_root H0). unfold toplevel_propagate in HTopLevel.
      rewrite HTopLevel in H2. subst. reflexivity.
    - apply IsPath_chunk in H1. destruct H1 as [e' [He Hf]].
      destruct (synth_sub_expr _ H0 He) as [t' [f' [[H3|H3] H4]]];
        rewrite H4; specialize (IHp (sub_expr_valid _ _ He) (f1 e p) (eq_refl _));
        specialize (H4 []); rewrite app_nil_r in H4; simpl in H4; rewrite H4 in IHp;
        destruct e'.
      + inv Hf.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv IHp; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv IHp; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts. inv Hf; inv H3. simpl. rewrite He; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3.
        * rewrite (max_l _ _ (synth_check_determine_order H7 H10 (le_refl _))) in *.
          rewrite H; simpl; _tac_spec_ts.
        * rewrite (max_r _ _ (synth_check_determine_order H10 H7 (le_refl _))) in *.
          rewrite H. destruct (synth_must_be_determine H10). simpl. rewrite <- H2.
          apply (check_root H7).
        * rewrite (max_l _ _ (synth_check_determine_order H7 H10 (le_refl _))) in *.
          rewrite H1. destruct (synth_must_be_determine H7). simpl. rewrite <- H2.
          apply (check_root H10).
        * rewrite (max_r _ _ (synth_check_determine_order H10 H7 (le_refl _))) in *.
          rewrite H1; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3.
        * rewrite H; simpl; _tac_spec_ts.
        * rewrite H1; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3. rewrite He; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv IHp; simpl; try _tac_spec_ts.
        rewrite H1; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl; rewrite HAssign.
        * destruct (synth_determine e'). rewrite (max_r _ _ (synth_check_order H H7)).
          apply (check_root H7).
        * destruct (synth_must_be_determine H5). subst.
          rewrite (max_l _ _ (lt_le_incl _ _ H8)). assumption.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv IHp; simpl. rewrite He; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv IHp; simpl; try _tac_spec_ts.
        * rewrite H5; simpl; _tac_spec_ts.
        * rewrite H5; simpl; _tac_spec_ts.
      + inv Hf. _gen_eq_spec_ts. inv H3. repeat gen_nth. rewrite HConcat. simpl.
        rewrite H. specialize (H5 _ _ _ _ H6 H2 H); simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3. simpl. rewrite HRepl; simpl; _tac_spec_ts.
      + inv Hf.
      + _gen_eq_spec_ts; inv Hf; inv H3; try (inv H2); inv IHp; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; try (inv H); inv IHp; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H1; simpl; rewrite He; simpl; _tac_spec_ts.
      + destruct (HComp _ _ _ _ He _ (eq_refl _)); inv Hf; inv H3; inv H5.
        * rewrite (max_l _ _ (synth_check_determine_order H9 H12 (le_refl _))) in *.
          rewrite H; simpl; _tac_spec_ts.
        * rewrite (max_r _ _ (synth_check_determine_order H12 H9 (le_refl _))) in *.
          rewrite H. destruct (synth_must_be_determine H12). simpl. rewrite <- H3.
          apply (check_root H9).
        * rewrite (max_l _ _ (synth_check_determine_order H9 H12 (le_refl _))) in *.
          rewrite H1. destruct (synth_must_be_determine H9). simpl. rewrite <- H3.
          apply (check_root H12).
        * rewrite (max_r _ _ (synth_check_determine_order H12 H9 (le_refl _))) in *.
          rewrite H1; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H5.
        * rewrite H; simpl; _tac_spec_ts.
        * rewrite H1; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H1; rewrite He; simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; try (inv H2); inv IHp; simpl; try _tac_spec_ts.
        rewrite H1. simpl; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H2; simpl; rewrite HAssign.
        * destruct (synth_determine e'). rewrite (max_r _ _ (synth_check_order H2 H9)).
          apply (check_root H9).
        * destruct (synth_must_be_determine H7). subst.
          rewrite (max_l _ _ (lt_le_incl _ _ H10)). assumption.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H2; inv IHp; simpl;
        rewrite He; _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; try (inv H2); inv IHp; simpl; try _tac_spec_ts.
        rewrite H5; _tac_spec_ts.
      + inv Hf. _gen_eq_spec_ts. inv H3. inv H1; repeat gen_nth. rewrite HConcat. simpl.
        rewrite H1. specialize (H9 _ _ _ _ H6 H3 H1); _tac_spec_ts.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H2; simpl. rewrite HRepl; _tac_spec_ts.
  Qed.

  Theorem ts_implies_spec : forall f1,
      propagate_def f1 -> forall e f2, e ==> (determine e) -| f2 ->
                                 forall p, IsPath e p -> forall n, f2 p = Some n -> f1 e p = n.
  Proof.
    induction p using path_ind; intros; propagate_def_split.
    - destruct (synth_must_be_determine H0). rewrite H3 in H2. inv H2. apply HTopLevel.
    - apply IsPath_chunk in H1. destruct H1 as [e' [He Hf]].
      specialize (IHp (sub_expr_valid _ _ He)).
      destruct (synth_sub_expr _ H0 He) as [t' [f' [[H3|H3] H4]]];
        assert (Hf': f2 p = f' []) by
        (specialize (H4 []); rewrite app_nil_r in H4; assumption);
        rewrite H4 in H2; destruct e'.
      + inv Hf.
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *; apply IHp in Hf'.
        * apply synth_root in H8. congruence.
        * apply check_root in H8. congruence.
        * apply check_root in H11. congruence.
        * apply synth_root in H11. congruence.
      + _gen_eq_spec_ts. inv Hf. rewrite He. apply IHp. inv H3. simpl in *.
        apply synth_root in H1. congruence.
      + _gen_eq_spec_ts. inv Hf. rewrite He. inv H3. simpl in *.
        destruct (synth_must_be_determine H1). congruence.
      + _gen_eq_spec_ts. inv Hf; inv H3.
        * rewrite (max_l _ _ (synth_check_determine_order H8 H11 (le_refl _))) in *.
          destruct (synth_must_be_determine H8). simpl in *. congruence.
        * rewrite (max_r _ _ (synth_check_determine_order H11 H8 (le_refl _))) in *.
          destruct (synth_must_be_determine H11). simpl in *.
          apply check_root in H8. congruence.
        * rewrite (max_l _ _ (synth_check_determine_order H8 H11 (le_refl _))) in *.
          destruct (synth_must_be_determine H8). simpl in *.
          apply check_root in H11. congruence.
        * rewrite (max_r _ _ (synth_check_determine_order H11 H8 (le_refl _))) in *.
          destruct (synth_must_be_determine H11). simpl in *. congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *.
        * destruct (synth_must_be_determine H8). congruence.
        * destruct (synth_must_be_determine H11). congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *;
        edestruct synth_must_be_determine; [ eassumption | congruence].
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *.
        * apply synth_root in H8. specialize (IHp _ Hf'). congruence.
        * edestruct synth_must_be_determine; [ eassumption | congruence].
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *; rewrite HAssign.
        * destruct (synth_determine e'). rewrite (max_r _ _ (synth_check_order H H8)).
          apply check_root in H8. congruence.
        * destruct (synth_must_be_determine H6). subst.
          rewrite (max_l _ _ (lt_le_incl _ _ H9)). congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *;
        destruct (synth_must_be_determine H8); congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *; apply IHp in Hf'.
        * destruct (synth_must_be_determine H10). congruence.
        * destruct (synth_must_be_determine H10). congruence.
        * apply synth_root in H13. congruence.
        * apply check_root in H13. congruence.
        * apply check_root in H14. congruence.
        * apply synth_root in H14. congruence.
      + inv Hf; _gen_eq_spec_ts; inv H3; inv H1; repeat gen_nth; simpl in *.
        rewrite H1 in *. specialize (H8 _ _ _ _ H6 H H1).
        destruct (synth_must_be_determine H8). congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; simpl in *;
        edestruct synth_must_be_determine; [ eassumption | congruence].
      + inv Hf.
      + _gen_eq_spec_ts; inv Hf; inv H3; try (inv H5); simpl in Hf'; apply IHp in Hf';
        simpl in H2; subst.
        * apply check_root in H8. congruence.
        * apply check_root in H11. congruence.
      + _gen_eq_spec_ts. inv Hf. rewrite He. apply IHp. inv H3. inv H.
        simpl in *. apply check_root in H1. congruence.
      + _gen_eq_spec_ts. inv Hf. rewrite He. inv H3. inv H1. simpl in *.
        destruct (synth_must_be_determine H7). simpl in *. congruence.
      + _gen_eq_spec_ts. inv Hf; inv H3; inv H7.
        * rewrite (max_l _ _ (synth_check_determine_order H10 H13 (le_refl _))) in *.
          destruct (synth_must_be_determine H10). simpl in *. congruence.
        * rewrite (max_r _ _ (synth_check_determine_order H13 H10 (le_refl _))) in *.
          destruct (synth_must_be_determine H13). simpl in *.
          apply check_root in H10. congruence.
        * rewrite (max_l _ _ (synth_check_determine_order H10 H13 (le_refl _))) in *.
          destruct (synth_must_be_determine H10). simpl in *.
          apply check_root in H13. congruence.
        * rewrite (max_r _ _ (synth_check_determine_order H13 H10 (le_refl _))) in *.
          destruct (synth_must_be_determine H13). simpl in *. congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H7; simpl in *.
        * destruct (synth_must_be_determine H10). congruence.
        * destruct (synth_must_be_determine H13). congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H1; simpl in *;
        edestruct synth_must_be_determine; [ eassumption | congruence].
      + _gen_eq_spec_ts; inv Hf; inv H3; try (inv H5); simpl in *.
        * apply check_root in H8. specialize (IHp _ Hf'). congruence.
        * edestruct synth_must_be_determine; [ eassumption | congruence].
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H5; simpl in *; rewrite HAssign.
        * destruct (synth_determine e'). rewrite (max_r _ _ (synth_check_order H3 H10)).
          apply check_root in H10. congruence.
        * destruct (synth_must_be_determine H8). subst.
          rewrite (max_l _ _ (lt_le_incl _ _ H11)). congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H5; simpl in *;
        destruct (synth_must_be_determine H10); congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; try (inv H6); simpl in *; apply IHp in Hf'.
        * destruct (synth_must_be_determine H10). congruence.
        * apply check_root in H13. congruence.
        * apply check_root in H14. congruence.
      + inv Hf; _gen_eq_spec_ts; inv H3; inv H1; repeat gen_nth; simpl in *.
        rewrite H1 in *. specialize (H10 _ _ _ _ H6 H3 H1).
        destruct (synth_must_be_determine H10). congruence.
      + _gen_eq_spec_ts; inv Hf; inv H3; inv H5; simpl in *;
        destruct (synth_must_be_determine H8); congruence.
  Qed.

  Theorem ts_equiv_spec : forall f1 f2 e,
      propagate_def f1 -> e ==> (determine e) -| f2 ->
      forall p, IsPath e p -> forall n, f2 p = Some n <-> f1 e p = n.
  Proof.
    split; intros.
    - apply (ts_implies_spec H H0 H1 H2).
    - apply (spec_implies_ts H H0 H1 H2).
  Qed.

End Equiv.

