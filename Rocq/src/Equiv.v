From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import Spec.
From Verilog Require Import TypeSystem.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.

Import Expr.
Import ExprPath.
Import Path.
Import Spec.
Import TypeSystem.
Import Utils.

Module Equiv.

  Definition agree e f1 (f2: path -> option nat) :=
    forall p, IsPath e p -> f2 p = Some (f1 p).

  Ltac antisym :=
    match goal with
    | [ H: ?x <= ?y, F: ?y <= ?x |- _ ] =>
        let nH := fresh in assert (nH: x = y) by apply (le_antisymm _ _ H F);
                           clear H; clear F
    end
  .

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
          apply (synth_check_determine_order H F (le_refl _)); try antisym
    | [ H: ?e <== ?t -| _, F: ?t <= determine ?e |- _ ] =>
        let nH := fresh in assert (nH: determine e = t) by
          apply (synth_and_order H F)
    end
  .

  Ltac _ts_gen :=
    match goal with
    | [ H: _ ==> ?t -| ?f |- _ ] =>
        destruct (synth_must_be_determine H); subst; clear H
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
      + repeat prop_gen_eq; try _gen_rel; repeat _ts_gen; congruence.
      + apply IsPath_chunk in H0. destruct H0 as [e' [Hse Hp]].
        destruct (synth_sub_expr _ Hs Hse) as [t' [f' [[H3|H3] H4]]];
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
          destruct (synth_sub_expr _ H F) as [t' [f' [[H3|H3] H4]]];
          repeat _ts_spec; inv_ts; simpl in *; repeat gen_nth; try _gen_rel;
          repeat _ts_gen; congruence || lia
      end
    .
    unfold agree. autounfold with Spec. repeat split; intros; try _crunch_ts_imp_spec.
    destruct (synth_must_be_determine H0); specialize (H [] (P_Empty _)); congruence.
  Qed.

  Theorem ts_equiv_spec : forall e f1,
      propagate_def e f1 <-> exists f2, agree e f1 f2 /\ exists t, e ==> t -| f2.
  Proof.
    split; intros.
    - apply (spec_implies_ts _ _ H).
    - destruct H as [f2 [H1 [t H2]]]. apply (ts_implies_spec _ _ _ _ H1 H2).
  Qed.

End Equiv.
