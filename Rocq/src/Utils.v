From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.

Import ListNotations.

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
        * inversion H1. subst. left. assert (HNat: i + 0 = i). lia. rewrite HNat. reflexivity.
        * right. apply IHl. exists n. exists x. intuition. assert (HNat: i + 1 + n = i + S n). lia.
          rewrite HNat. apply H2.
  Qed.

  Lemma mapI_values:  forall (X Y: Type) (f: nat -> X -> Y) (l: list X) y,
      In y (mapI f l) <-> exists n x, nth_error l n = Some x /\ y = f n x.
  Proof.
    intros. unfold mapI.  apply mapI'_values.
  Qed.

End Utils.
