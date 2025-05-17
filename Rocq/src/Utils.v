From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Classes.RelationClasses.

Import Nat.
Import ListNotations.

Module Utils.

  Ltac inv H := inversion H; clear H; subst.

  Ltac antisym :=
    match goal with
    | [ H: ?x <= ?y, F: ?y <= ?x |- _ ] =>
        let nH := fresh in assert (nH: x = y) by apply (le_antisymm _ _ H F);
                           clear H; clear F
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

  Definition list_sep {T: Type} (l: list T) :=
    match l with
    | [] => None
    | hd :: _ => Some (removelast l, last l hd)
    end
  .

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
        apply app_removelast_last with (d := t0) in HlNil. rewrite HlNil in H.
        rewrite app_inj_tail_iff in H. destruct H. subst. reflexivity.
  Qed.

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

  Lemma max_dec_bis : forall a b, {max a b = a /\ b <= a} + {max a b = b /\ a <= b}.
  Proof.
    intros.
    destruct (max_dec a b).
    - rewrite e. left. split. reflexivity. apply max_l_iff. assumption.
    - rewrite e. right. split. reflexivity. apply max_r_iff. assumption.
  Qed.

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
