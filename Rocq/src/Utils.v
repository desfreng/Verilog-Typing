From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Classes.RelationClasses.

Import Nat.
Import ListNotations.

Module Learn.
  (* Taken from coq-tricks *)
  Inductive Learnt {P:Prop} :=
  | AlreadyLearnt (H:P).

  Local Ltac learn_fact H :=
    let P := type of H in
    lazymatch goal with
    | [ Hlearnt: @Learnt P |- _ ] =>
      fail 0 "already knew" P "through" Hlearnt
    | _ => pose proof H; pose proof (AlreadyLearnt H)
    end.

  Tactic Notation "learn" constr(H) := learn_fact H.
End Learn.

Module Utils.
  Import Learn.

  Ltac inv H := inversion H; clear H; subst.

  Ltac antisym :=
    match goal with
    | [ H: ?x <= ?y, F: ?y <= ?x |- _ ] =>
        learn (le_antisymm _ _ H F)
    end
  .

  Ltac splitHyp :=
    match goal with
    | [ H: _ /\ _ |- _ ] => destruct H
    end
  .

  Ltac existsHyp :=
    match goal with
    | [ H: ex _ |- _ ] => destruct H
    end
  .

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

  Definition list_sep {T: Type} (l: list T) :=
    match l with
    | [] => None
    | hd :: _ => Some (removelast l, last l hd)
    end
  .

  Definition le_option_nat (x y : option nat) : Prop :=
    match x, y with
    | None, _ => True
    | Some _, None => False
    | Some a, Some b => a <= b
    end.

  Instance le_option_nat_Reflexive : Reflexive le_option_nat.
  Proof.
    intros [n|]; simpl; auto.
  Qed.

  Lemma max_dec_bis: forall a b, (max a b = a /\ b <= a) \/ (max a b = b /\ a <= b).
  Proof.
    intros.
    destruct (max_dec a b).
    - rewrite e. left. split. reflexivity. apply max_l_iff. assumption.
    - rewrite e. right. split. reflexivity. apply max_r_iff. assumption.
  Qed.

  Ltac _useMaxDecBis :=
    match goal with
    | [ H: (_ = _ /\ _) \/ (_ = _ /\ _) |- _ ] =>
        destruct H as [[?Heq ?H]|[?Heq ?H]]; rewrite Heq in *; clear Heq
    end
  .

  Ltac splitMax :=
    match goal with
    | [ H: context[max ?x ?y] |- _ ] => learn (max_dec_bis x y); _useMaxDecBis
    | [ |- context[max ?x ?y] ] => learn (max_dec_bis x y); _useMaxDecBis
    end
  .

  Lemma nth_error_lists : forall A B (l: list A) (l': list B) n x,
      nth_error l n = Some x -> length l = length l' -> exists y, nth_error l' n = Some y.
  Proof.
    induction l; intros.
    - destruct n; discriminate H.
    - destruct l'. discriminate H0. inv H0. destruct n.
      + eexists. reflexivity.
      + firstorder.
  Qed.

  Ltac gen_nth :=
    match goal with
    | [ Hlen: length ?l1 = length ?l2, Hnth: nth_error ?l1 ?n = Some _ |- _ ] =>
        destruct (nth_error_lists _ _ _ _ _ _ Hnth Hlen); clear Hlen
    | [ Hlen: length ?l2 = length ?l1, Hnth: nth_error ?l1 ?n = Some _ |- _ ] =>
        let HnewTh := fresh in assert(HnewTh: exists y, nth_error l2 n = Some y) by
          (apply (nth_error_lists _ _ _ _ _ _ Hnth); symmetry; apply Hlen);
                               destruct HnewTh; clear Hlen
    end
  .

  Lemma option_eq_dec : forall (T: Type) (x y: option T),
      (forall x y: T, {x = y} + {x <> y}) -> {x = y} + {x <> y}.
  Proof.
    intros. destruct x; destruct y; try (destruct (X t0 t1)); subst;
      left + right; congruence.
  Qed.
End Utils.
