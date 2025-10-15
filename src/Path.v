From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lia.

From Verilog Require Import Utils.

Import ListNotations.
Import Wf_nat.

Import Utils.

(** * Path Module *)

(** This module defines and manipulates paths, represented as lists of natural numbers.
    It provides basic structural operations (like splitting and equality),
    as well as a custom induction principle based on list suffix decomposition. *)
Module Path.
  (** ** Definition of Paths *)
  (** A [path] is represented as a list of natural numbers. *)
  Definition path := list nat.

  (** ** Path Splitting *)
    
  (** [path_sep] decomposes a non-empty list into its prefix (all elements except the last)
      and its final element. It returns [None] if the list is empty. *)
  Definition path_sep {T: Type} (l: list T) :=
    match l with
    | [] => None
    | hd :: _ => Some (removelast l, last l hd)
    end.

  (** ** Properties of [path_sep] *)

  (** [path_sep_None]: [path_sep l] yields [None] if and only if [l] is empty. *)
  Lemma path_sep_None : forall T (l: list T), path_sep l = None <-> l = [].
  Proof.
    split; intros.
    - destruct l; [reflexivity | discriminate H].
    - subst. reflexivity.
  Qed.

  (** [removelast_length]: Removing the last element of a non-empty list strictly reduces its length. *)
  Lemma removelast_length : forall T (l: list T), l <> [] -> length (removelast l) < length l.
  Proof.
    induction l; intros.
    - contradiction.
    - simpl. destruct l eqn:Hl.
      + lia.
      + rewrite <- Hl in *. simpl. apply Arith_base.lt_n_S_stt. apply IHl.
        rewrite Hl. unfold not. intros. discriminate H0.
  Qed.

  (** [path_sep_Some]: When [path_sep l] = [Some (l', x)], the list [l] equals [l' ++ [x]],
    and the length of [l'] is strictly less than that of [l]. *)
  Lemma path_sep_Some : forall T (l: list T) x l',
      path_sep l = Some (l', x) <-> l = l' ++ [x] /\ length l' < length l.
  Proof.
    split; intros.
    - destruct l eqn:Hl.
      + discriminate H.
      + unfold path_sep in H. rewrite <- Hl in *. inversion H. split.
        * apply app_removelast_last. unfold not. intros. subst. discriminate H0.
        * apply removelast_length. subst. discriminate.
    - destruct l eqn:Hl; destruct H.
      + apply app_cons_not_nil in H. contradiction.
      + unfold path_sep. rewrite <- Hl in *. assert (HlNil: l <> []). subst. discriminate.
        apply app_removelast_last with (d := t) in HlNil. rewrite HlNil in H.
        rewrite app_inj_tail_iff in H. destruct H. subst. reflexivity.
  Qed.

  (** ** Induction Principle on Paths *)
  
  (**
    [path_ind] defines a structural induction principle for paths that proceeds
    by successively removing the last element of the list.
    It enables reasoning over paths constructed by appending elements at the end,
    rather than at the front. *)
  Theorem path_ind : forall (P : path -> Prop), P [] -> (forall x l, P l -> P (l ++ [x])) -> forall p, P p.
  Proof.
    intros. induction p using (induction_ltof1 _ (@length _)). unfold ltof in H1.
    destruct (path_sep x) as [[a b]|] eqn:Hp.
    - apply path_sep_Some in Hp. destruct Hp as [Hp Hlen].
      rewrite Hp. apply H0. apply H1. assumption.
    - apply path_sep_None in Hp. subst. assumption.
  Qed.

  (** ** Decidability *)
  
  (** [path_eq_dec]: Equality over paths (lists of naturals) is decidable. *)
  Theorem path_eq_dec : forall (a b: path), {a = b} + {a <> b}.
  Proof. decide equality. decide equality. Qed.
End Path.
