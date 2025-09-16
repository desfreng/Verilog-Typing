From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lia.

From Verilog Require Import Utils.

Import ListNotations.
Import Wf_nat.

Import Utils.

Module Path.
  Definition path := list nat.


  Lemma list_sep_None : forall T (l: list T), list_sep l = None <-> l = [].
  Proof.
    split; intros.
    - destruct l; [reflexivity | discriminate H].
    - subst. reflexivity.
  Qed.

  Lemma removelast_length : forall T (l: list T), l <> [] -> length (removelast l) < length l.
  Proof.
    induction l; intros.
    - contradiction.
    - simpl. destruct l eqn:Hl.
      + lia.
      + rewrite <- Hl in *. simpl. apply Arith_base.lt_n_S_stt. apply IHl.
        rewrite Hl. unfold not. intros. discriminate H0.
  Qed.

  Lemma list_sep_Some : forall T (l: list T) x l',
      list_sep l = Some (l', x) <-> l = l' ++ [x] /\ length l' < length l.
  Proof.
    split; intros.
    - destruct l eqn:Hl.
      + discriminate H.
      + unfold list_sep in H. rewrite <- Hl in *. inversion H. split.
        * apply app_removelast_last. unfold not. intros. subst. discriminate H0.
        * apply removelast_length. subst. discriminate.
    - destruct l eqn:Hl; destruct H.
      + apply app_cons_not_nil in H. contradiction.
      + unfold list_sep. rewrite <- Hl in *. assert (HlNil: l <> []). subst. discriminate.
        apply app_removelast_last with (d := t) in HlNil. rewrite HlNil in H.
        rewrite app_inj_tail_iff in H. destruct H. subst. reflexivity.
  Qed.

  Theorem path_ind : forall (P : path -> Prop), P [] -> (forall x l, P l -> P (l ++ [x])) -> forall p, P p.
  Proof.
    intros. induction p using (induction_ltof1 _ (@length _)). unfold ltof in H1.
    destruct (list_sep x) as [[a b]|] eqn:Hp.
    - apply list_sep_Some in Hp. destruct Hp as [Hp Hlen].
      rewrite Hp. apply H0. apply H1. assumption.
    - apply list_sep_None in Hp. subst. assumption.
  Qed.

  Theorem path_eq_dec : forall (a b: path), {a = b} + {a <> b}.
  Proof. decide equality. decide equality.  Qed.

End Path.
