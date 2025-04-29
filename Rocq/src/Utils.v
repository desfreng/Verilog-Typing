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
    intros. unfold mapI. apply mapI'_values.
  Qed.

  Fixpoint maxList x l :=
    match l with
    | [] => x
    | hd :: tl => max hd (maxList x tl)
    end
  .

  Lemma maxList_order : forall x hd tl, hd <= x -> max hd (maxList x tl) = maxList x tl.
  Proof.
    intros. generalize dependent x. generalize dependent hd. induction tl.
    - apply max_r.
    - intros. simpl. destruct (le_ge_dec a (maxList x tl)).
      + rewrite -> (max_r _ _ l). apply (IHtl _ _ H).
      + rewrite -> (max_l _ _ g). apply max_r. clear IHtl. induction tl.
        * apply (le_trans _ _ _ H g).
        * apply IHtl. apply (max_lub_r _ _ _ g).
  Qed.

  Lemma maxList_val : forall x l, maxList x l = x \/ (exists e, In e l /\ maxList x l = e).
  Proof.
    induction l.
    - left. reflexivity.
    - destruct IHl.
      + destruct (le_ge_dec a x).
        * left. simpl. rewrite (maxList_order _ _ _ l0). assumption.
        * right. exists a. firstorder. simpl. apply max_l. rewrite <- H in g. assumption.
      + destruct H as [e [H1 H2]]. destruct (le_ge_dec a e).
        * right. exists e. split. right. assumption. simpl. subst. apply max_r. assumption.
        * right. exists a. firstorder. simpl. apply max_l. subst. assumption.
  Qed.

  Lemma maxList_is_max_l : forall x l, x <= maxList x l.
  Proof.
    induction l.
    - constructor.
    - apply le_trans with (m := maxList x l). assumption. apply le_max_r.
  Qed.

  Lemma maxList_is_max_r : forall x l e, In e l -> e <= maxList x l.
  Proof.
    induction l; intros.
    - inversion H.
    - destruct H.
      + subst. apply le_max_l.
      + apply le_trans with (m := maxList x l). firstorder. apply le_max_r.
  Qed.

  Fixpoint sum (l: list nat) :=
    match l with
    | [] => 0
    | hd :: tl => hd + sum tl
    end
  .

  Lemma and_with_impl : forall P Q, P -> (P -> Q) -> P /\ Q.
  Proof.
    split; intros; auto.
  Qed.

  Ltac splitAnd :=
    match goal with
    | [ |- _ /\ _ ] => apply and_with_impl; [idtac|intros]
    end
  .
End Utils.
