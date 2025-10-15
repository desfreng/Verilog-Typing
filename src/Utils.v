From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Classes.RelationClasses.

Import Nat.
Import ListNotations.

(** Module imported from coq-tricks.
    Provides a mechanism to store learnt hypotheses to avoid re-deriving
    the same facts repeatedly during proof automation. *)
Module Learn.
  (** A wrapper type used to record that a proposition [P] has been learnt. *)
  Inductive Learnt {P:Prop} :=
  | AlreadyLearnt (H:P).

  (** Internal tactic: marks a hypothesis as learnt if it hasn’t been recorded yet. *)
  Local Ltac learn_fact H :=
    let P := type of H in
    lazymatch goal with
    | [ Hlearnt: @Learnt P |- _ ] =>
      fail 0 "already knew" P "through" Hlearnt
    | _ => pose proof H; pose proof (AlreadyLearnt H)
    end.

  (** Public interface for [learn_fact]. 
      Usage: [learn H] records the fact [H] as already known. *)
  Tactic Notation "learn" constr(H) := learn_fact H.
End Learn.

(** Utility module providing:
    - Custom Ltac tactics for common proof patterns.
    - Helper lemmas for reasoning about lists and natural numbers.
    - Definitions of indexed mapping functions and option-based ordering. *)
Module Utils.
  Import Learn.

  (** ** Custom tactics *)

  (** [inv H]: performs inversion on hypothesis [H], clears it, and substitutes
      resulting equalities into the context. *)
  Ltac inv H := inversion H; clear H; subst.

  (** [antisym]: applies antisymmetry on a pair of [<=] relations in the context
      and records the resulting equality using [learn]. *)
  Ltac antisym :=
    match goal with
    | [ H: ?x <= ?y, F: ?y <= ?x |- _ ] =>
        learn (le_antisymm _ _ H F)
    end.

  (** [splitHyp]: destructs a conjunction in the context. *)
  Ltac splitHyp :=
    match goal with
    | [ H: _ /\ _ |- _ ] => destruct H
    end.
  
  (** [existsHyp]: destructs an existential hypothesis in the context. *)
  Ltac existsHyp :=
    match goal with
    | [ H: ex _ |- _ ] => destruct H
    end.

  (** Lemma and tactic to help build conjunctions incrementally. *)
  Lemma and_with_impl : forall P Q, P -> (P -> Q) -> P /\ Q.
  Proof.
    split; intros; auto.
  Qed.

  (** [splitAnd]: prepares the goal for proving a conjunction by introducing
      the left-hand side immediately and the right-hand side later. *)
  Ltac splitAnd :=
    match goal with
    | [ |- _ /\ _ ] => apply and_with_impl; [idtac|intros]
    end.

  (** ** Reasoning on [max] *)

  (** Decomposes the [max] function into explicit cases, preserving order relations. *)
  Lemma max_dec_bis: forall a b, (max a b = a /\ b <= a) \/ (max a b = b /\ a <= b).
  Proof.
    intros.
    destruct (max_dec a b).
    - rewrite e. left. split. reflexivity. apply max_l_iff. assumption.
    - rewrite e. right. split. reflexivity. apply max_r_iff. assumption.
  Qed.

  (** Auxiliary tactic used by [splitMax] to destruct results of [max_dec_bis]. *)
  Ltac _useMaxDecBis :=
    match goal with
    | [ H: (_ = _ /\ _) \/ (_ = _ /\ _) |- _ ] =>
        destruct H as [[?Heq ?H]|[?Heq ?H]]; rewrite Heq in *; clear Heq
    end.

  (** [splitMax]: applies [max_dec_bis] to all occurrences of [max x y] in either
      the goal or context, and simplifies the resulting branches. *)
  Ltac splitMax :=
    match goal with
    | [ H: context[max ?x ?y] |- _ ] => learn (max_dec_bis x y); _useMaxDecBis
    | [ |- context[max ?x ?y] ] => learn (max_dec_bis x y); _useMaxDecBis
    end.

  (** ** List reasoning *)

  (** Lemma stating that if two lists have the same length, then for every element
      in one list accessible via [nth_error], there exists a corresponding element
      at the same index in the other list. *)
  Lemma nth_error_lists : forall A B (l: list A) (l': list B) n x,
      nth_error l n = Some x -> length l = length l' -> exists y, nth_error l' n = Some y.
  Proof.
    induction l; intros.
    - destruct n; discriminate H.
    - destruct l'. discriminate H0. inv H0. destruct n.
      + eexists. reflexivity.
      + firstorder.
  Qed.

  (** [gen_nth]: given two lists of equal length and an index known to exist in one,
      generates the corresponding element in the other list. *)
  Ltac gen_nth :=
    match goal with
    | [ Hlen: length ?l1 = length ?l2, Hnth: nth_error ?l1 ?n = Some _ |- _ ] =>
        destruct (nth_error_lists _ _ _ _ _ _ Hnth Hlen); clear Hlen
    | [ Hlen: length ?l2 = length ?l1, Hnth: nth_error ?l1 ?n = Some _ |- _ ] =>
        let HnewTh := fresh in assert(HnewTh: exists y, nth_error l2 n = Some y) by
          (apply (nth_error_lists _ _ _ _ _ _ Hnth); symmetry; apply Hlen);
                               destruct HnewTh; clear Hlen
    end.
  
  (** ** Indexed mapping function *)

  (** [mapI'] applies a function [f] to each element of a list [l],
      passing its index (starting from [i]) as an additional argument. *)
  Fixpoint mapI'{X Y: Type} f i (l: list X) : list Y :=
    match l with
    | [] => []
    | hd :: tl => f i hd :: mapI' f (i + 1) tl
    end.

  (** [mapI] is a specialization of [mapI'] starting from index 0. *)
  Definition mapI {X Y: Type} (f: nat -> X -> Y) := mapI' f 0.

  (** Characterization of elements in [mapI']: 
      an element [y] appears in [mapI' f i l] iff there exists an index [n]
      and element [x] such that [nth_error l n = Some x] and [y = f (i + n) x]. *)
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

  (** Simplified version of [mapI'_values] for the common case where indexing starts at 0. *)
  Lemma mapI_values :  forall (X Y: Type) (f: nat -> X -> Y) (l: list X) y,
      In y (mapI f l) <-> exists n x, nth_error l n = Some x /\ y = f n x.
  Proof.
    intros. unfold mapI. apply mapI'_values.
  Qed.
  
  (** ** Custom helper functions *)

  (** Computes the sum of a list of natural numbers. *)
  Fixpoint sum (l: list nat) :=
    match l with
    | [] => 0
    | hd :: tl => hd + sum tl
    end.

  (** Defines an ordering relation on optional natural numbers,
      treating [None] as the smallest element. *)
  Definition le_option_nat (x y : option nat) : Prop :=
    match x, y with
    | None, _ => True
    | Some _, None => False
    | Some a, Some b => a <= b
    end.

  (** [le_option_nat] is reflexive. *)
  Instance le_option_nat_Reflexive : Reflexive le_option_nat.
  Proof.
    intros [n|]; simpl; auto.
  Qed.
End Utils.
