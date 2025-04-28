From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.
Import Nat.

Module Utils.

  Ltac inv H := inversion H; clear H; subst.

  Fixpoint mapI'{X Y: Type} f i (l: list X) : list Y :=
    match l with
    | [] => []
    | hd :: tl => f i hd :: mapI' f (i + 1) tl
    end
  .

  Definition mapI {X Y: Type} (f: nat -> X -> Y) := mapI' f 0.

  Lemma mapI'_values : forall (X Y: Type) (f: nat -> X -> Y) (l: list X) y i,
      In y (mapI' f i l) <-> exists n x, nth_error l n = Some x /\ y = f (i + n) x.
  Proof.
    induction l.
    - split; intros. contradiction. destruct H as [[|n] [x [H1 H2]]]; discriminate H1.
    - split; intros.
      + destruct H as [H1 | H2].
        * exists 0. exists a. intuition. assert (HNat: i + 0 = i). lia. rewrite HNat. auto.
        * rewrite IHl in H2. destruct H2 as [n [x [H1 H2]]].
          exists (1 + n). exists x. intuition. assert (HNat: i + (1 + n) = i + 1 + n). lia.
          rewrite HNat. apply H2.
      + destruct H as [n [x [H1 H2]]]. destruct n.
        * inversion H1. subst. left. assert (HNat: i + 0 = i). lia. rewrite HNat.
          reflexivity.
        * right. apply IHl. exists n. exists x. intuition. assert (HNat: i + 1 + n = i + S n). lia.
          rewrite HNat. apply H2.
  Qed.

  Lemma mapI_values :  forall (X Y: Type) (f: nat -> X -> Y) (l: list X) y,
      In y (mapI f l) <-> exists n x, nth_error l n = Some x /\ y = f n x.
  Proof.
    intros. unfold mapI.  apply mapI'_values.
  Qed.

  Definition max_list x l := forall e, In e l -> e <= x.

  Lemma max_in_list : forall x l, max_list x l \/ (exists e, In e l /\ max_list e l /\ x <= e).
  Proof.
    unfold max_list. induction l; intros.
    - left. intros. inv H.
    - inv IHl.
      + destruct (le_ge_dec a x).
        * left. intros. inv H0; firstorder.
        * right. exists a. split. firstorder. split. intros. inv H0. reflexivity.
          apply le_trans with (m := x). firstorder. assumption. assumption.
      + destruct H as [m [H1 [H2 H3]]]. destruct (le_ge_dec a m).
        * right. exists m. split. firstorder. split. intros. inv H. assumption. firstorder.
          assumption.
        * right. exists a. split. firstorder. split. intros. inv H. reflexivity.
          apply le_trans with (m := m). firstorder. assumption.
          apply le_trans with (m := m). assumption. assumption.
  Qed.
End Utils.
