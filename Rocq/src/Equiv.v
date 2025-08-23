From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import Spec.
From Verilog Require Import TypeSystem.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.
Import Compare_dec.

Import Expr.
Import ExprPath.
Import Path.
Import Spec.
Import TypeSystem.
Import Utils.

Module Equiv.
  Theorem synth_determine : forall e, exists f, e ==> determine e -| f.
  Proof.
    induction e using Expr_ind; repeat existsHyp;
      try (eexists; econstructor; eassumption || reflexivity).
    - destruct (max_dec_bis (determine e1) (determine e2)) as [[H1 H2]|[H1 H2]].
      + destruct (synth_can_check _ _ _ _ H H2). eexists. simpl. rewrite H1.
        econstructor; eassumption || reflexivity.
      + destruct (synth_can_check _ _ _ _ H0 H2). eexists. simpl. rewrite H1.
        econstructor; eassumption || reflexivity.
    - destruct (max_dec_bis (determine e1) (determine e2)) as [[H1 H2]|[H1 H2]].
      + destruct (synth_can_check _ _ _ _ H H2).
        eexists; econstructor; eassumption || reflexivity.
      + destruct (synth_can_check _ _ _ _ H0 H2).
        eexists; econstructor; eassumption || reflexivity.
    - destruct (le_gt_dec (determine e) op).
      + destruct (synth_can_check _ _ _ _ H l). eexists.
        eapply LAssignS; eassumption || reflexivity.
      + eexists. eapply RAssignS; eassumption || reflexivity.
    - destruct (max_dec_bis (determine e2) (determine e3)) as [[H2 H3]|[H2 H3]].
      + destruct (synth_can_check _ _ _ _ H H3). eexists. simpl. rewrite H2.
        eapply LCondS; eassumption || reflexivity.
      + destruct (synth_can_check _ _ _ _ H0 H3). eexists. simpl. rewrite H2.
        eapply RCondS; eassumption || reflexivity.
    - assert (Hfs: exists fs, length fs = length args /\ forall n e t f,
                   nth_error args n = Some e ->
                   nth_error (map determine args) n = Some t ->
                   nth_error fs n = Some f -> e ==> t -| f).
      + induction args.
        * eexists []. split. reflexivity. intros []; intros; discriminate H0.
        * edestruct IHargs. intros. destruct (H (S n) e H0). exists x. assumption.
          destruct H0. destruct (H 0 a). reflexivity. exists (x0 :: x). split.
          -- simpl. rewrite H0. reflexivity.
          -- intros. destruct n. inv H3. inv H4. inv H5. assumption.
             simpl in *. firstorder.
      + destruct Hfs as [fs [H1 H2]]. eexists.
        eapply ConcatS with (ts := map determine args).
        * symmetry. apply length_map.
        * symmetry. eassumption.
        * assumption.
        * reflexivity.
        * reflexivity.
  Qed.

  Lemma synth_must_be_determine : forall e t f,
      e ==> t -| f -> t = determine e /\ f [] = Some (determine e).
  Proof.
    intros. splitAnd.
    - destruct (synth_determine e). apply (synth_inj _ _ _ _ _ H H0).
    - rewrite (synth_root _ _ _ H). subst. reflexivity.
  Qed.

  Lemma synth_check_determine_order : forall e1 e2 t1 t2 f1 f2,
      e1 ==> t1 -| f1 -> e2 <== t2 -| f2 -> t2 <= t1 -> determine e2 <= determine e1.
  Proof.
    intros. destruct (synth_must_be_determine _ _ _ H) as [Ht Hf].
    subst. destruct (synth_determine e2).
    apply (synth_check_order _ _ _ _ _ H2) in H0. apply (le_trans _ _ _ H0 H1).
  Qed.

  Lemma synth_and_order : forall e f t,
      e <== t -| f -> t <= determine e -> determine e = t.
  Proof.
    intros.
    apply le_antisymm.
    - destruct (always_synth e) as [t1 [f1 H1]].
      destruct (synth_must_be_determine _ _ _ H1).
      subst. apply (synth_check_order _ _ _ _ _ H1 H).
    - assumption.
  Qed.

  Definition agree e f1 (f2: path -> option nat) :=
    forall p, IsPath e p -> f2 p = Some (f1 p).

  Ltac _gen_rel :=
    match goal with
    | [ H: _ = max ?n ?m |- _ ] =>
        let nH := fresh in destruct (max_dec_bis n m) as [[nH ?]|[nH ?]];
                           rewrite nH in *; clear nH; try _gen_rel
    | [ |- _ = max ?n ?m ] =>
        let nH := fresh in destruct (max_dec_bis n m) as [[nH ?]|[nH ?]];
                           rewrite nH in *; clear nH; try _gen_rel
    | [ H: ?e1 ==> ?t -| _, F: ?e2 <== ?t -| _ |- _ ] =>
        let nH := fresh in assert (nH: determine e2 <= determine e1) by
          apply (synth_check_determine_order _ _ _ _ _ _ H F (le_refl _)); try antisym
    | [ H: ?e <== ?t -| _, F: ?t <= determine ?e |- _ ] =>
        let nH := fresh in assert (nH: determine e = t) by
          apply (synth_and_order _ _ _ H F)
    end
  .

  Ltac _ts_gen :=
    match goal with
    | [ H: _ ==> ?t -| ?f |- _ ] =>
        destruct (synth_must_be_determine _ _ _ H); subst; clear H
    | [ H: _ <== ?t -| ?f |-  _ ] =>
        apply check_root in H
    | [ H: forall _ _ _ _, _ -> _ -> _ -> _ ==> _ -| _,
          He: nth_error _ _ = Some ?e,
          Ht: nth_error _ _ = Some ?t,
          Hf: nth_error _ _ = Some ?f
          |- _ ] => specialize (H _ _ _ _ He Ht Hf)
    | [ H: nth_error _ _ = Some _ |- _ ] => rewrite H in *
    end
  .

  Lemma spec_implies_ts: forall e f1,
      propagate_def e f1 -> exists f2, agree e f1 f2 /\ exists t, e ==> t -| f2.
  Proof.
    intros. destruct (always_synth e) as [t [f Hs]]. exists f. split.
    - subst. unfold agree. intros. prop_split. induction p using path_ind.
      + repeat prop_gen_eq; try _gen_rel; repeat _ts_gen. congruence.
      + apply IsPath_chunk in H0. destruct H0 as [e' [Hse Hp]].
        destruct (synth_sub_expr _ _ _ _ _ Hs Hse) as [t' [f' [[H3|H3] H4]]];
        rewrite H4; specialize (IHp (sub_expr_valid _ _ _ Hse));
        specialize (H4 []); rewrite app_nil_r in H4; simpl in H4; rewrite H4 in IHp;
          destruct e'; inv Hp; inv_ts; simpl in *; repeat prop_gen_eq; try _gen_rel;
          repeat gen_nth; repeat _ts_gen; congruence || lia.
    - exists t. assumption.
  Qed.

  Lemma ts_implies_spec: forall e f1 f2 t,
      agree e f1 f2 -> e ==> t -| f2 -> propagate_def e f1.
  Proof.
    Ltac _ts_spec :=
      match goal with
      | [ H: ?e @[?p] = Some _ |- ?f (?p ++ [?x]) = _ ] =>
          assert (Hpx: IsPath e (p ++ [x])) by
          (apply IsPath_chunk; eexists; split;
           [apply H | econstructor; try eassumption; constructor]);
          assert (Hp: IsPath e p) by apply (sub_expr_valid _ _ _ H)
      | [ H: IsPath _ _, F: forall _, IsPath _ _ -> _ |- _ ] =>
          apply F in H
      | [ H: forall _,  _ = _ |- ?f (?p ++ [?x]) = _ ] =>
          specialize (H []) as HNil; rewrite app_nil_r in *;
          specialize (H [x]) as Hx
      end
    .
    Ltac _crunch_ts_imp_spec :=
      match goal with
      | [ H: _ ==> _ -| _, F: _ @[_] = Some _ |- _ ] =>
          destruct (synth_sub_expr _ _ _ _ _ H F) as [t' [f' [[H3|H3] H4]]];
          repeat _ts_spec; inv_ts; simpl in *; repeat gen_nth; try _gen_rel;
          repeat _ts_gen; congruence || lia
      end
    .
    unfold agree. autounfold with Spec. repeat split; intros; try _crunch_ts_imp_spec.
    destruct (synth_must_be_determine _ _ _ H0); specialize (H [] (P_Empty _));
      congruence.
  Qed.

  Theorem ts_equiv_spec : forall e f1,
      propagate_def e f1 <-> exists f2, agree e f1 f2 /\ exists t, e ==> t -| f2.
  Proof.
    split; intros.
    - apply (spec_implies_ts _ _ H).
    - destruct H as [f2 [H1 [t H2]]]. apply (ts_implies_spec _ _ _ _ H1 H2).
  Qed.

End Equiv.
