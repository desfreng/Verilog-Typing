From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Logic.Decidable.

From Verilog Require Import Expr.
From Verilog Require Import Path.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.
Import Expr.
Import Path.
Import Utils.

Set Implicit Arguments.

Module BiDir.

  Inductive Resizable : Expr -> Prop :=
  | ResAtom : forall op, Resizable (EAtom op)
  | ResCast : forall e, Resizable (ECast e)
  | ResComp : forall lhs rhs, Resizable (EComp lhs rhs)
  | ResLogic : forall lhs rhs, Resizable (ELogic lhs rhs)
  | ResRed : forall e, Resizable (EReduction e)
  | ResAssign : forall lval arg, Resizable (EAssign lval arg)
  | ResShiftAssign : forall lval arg, Resizable (EShiftAssign lval arg)
  | ResConcat : forall args, Resizable (EConcat args)
  | ResRepl : forall amount arg, Resizable (ERepl amount arg)
  | ResInside : forall arg args, Resizable (EInside arg args)
  .

  Fixpoint sum (l: list nat) :=
    match l with
    | [] => 0
    | hd :: tl => hd + sum tl
    end
  .

  Reserved Notation "e '==>' t" (at level 70).
  Reserved Notation "e '<==' t" (at level 70).

  Inductive synth : Expr -> nat -> Prop :=
  | AtomS op : EAtom op ==> op

  | LBinOpS a b t :
      a ==> t ->
      b <== t ->
      EBinOp a b ==> t

  | RBinOpS a b t :
      a <== t ->
      b ==> t ->
      EBinOp a b ==> t

  | UnOpS e t :
    e ==> t ->
    EUnOp e ==> t

  | CastS e t :
    e ==> t ->
    ECast e ==> t

  | LCompS a b t :
    a ==> t ->
    b <== t ->
    EComp a b ==> 1

  | RCompS a b t :
    a <== t ->
    b ==> t ->
    EComp a b ==> 1

  | LogicS a b ta tb :
    a ==> ta ->
    b ==> tb ->
    ELogic a b ==> 1

  | RedS e t :
    e ==> t ->
    EReduction e ==> 1

  | ShiftS a b t tb :
    a ==> t ->
    b ==> tb ->
    EShift a b ==> t

  | LAssignS lval e :
    e <== lval ->
    EAssign lval e ==> lval

  | RAssignS lval e te :
    e ==> te ->
    lval < te ->
    EAssign lval e ==> lval

  | ShiftAssignS lval e te :
    e ==> te ->
    EShiftAssign lval e ==> lval

  | LCondS e a b t te :
    e ==> te ->
    a ==> t ->
    b <== t ->
    ECond e a b ==> t

  | RCondS e a b t te :
    e ==> te ->
    a <== t ->
    b ==> t ->
    ECond e a b ==> t

  | ConcatS args ts t :
    length args = length ts ->
    (forall n e te, nth_error args n = Some e -> nth_error ts n = Some te -> e ==> te) ->
    t = sum ts ->
    EConcat args ==> t

  | ReplS i e te t :
    e ==> te ->
    t = i * te ->
    ERepl i e ==> t

  | LInsideS a args t :
    a ==> t ->
    (forall n e, nth_error args n = Some e -> e <== t) ->
    EInside a args ==> 1

  | RInsideS a args t :
    (exists e, In e args /\ e ==> t) ->
    a <== t ->
    (forall n e, nth_error args n = Some e -> e <== t) ->
    EInside a args ==> 1

  where "e '==>' n" := (synth e n)

  with check : Expr -> nat -> Prop :=
  | ResizeC e s t :
      Resizable e ->
      e ==> s ->
      s <= t ->
      e <== t

  | BinOpC a b t :
      a <== t ->
      b <== t ->
      EBinOp a b <== t

  | UnOpC e t :
      e <== t ->
      EUnOp e <== t

  | ShiftC a b t tb :
      a <== t ->
      b ==> tb ->
      EShift a b <== t

  | CondC e a b t te :
      e ==> te ->
      a <== t ->
      b <== t ->
      ECond e a b <== t

  where "e '<==' n" := (check e n)
  .


  Lemma concat_args: forall args t1 t2,
      (forall n e, nth_error args n = Some e -> forall t1 t2 : nat, e ==> t1 -> e ==> t2 -> t1 = t2) ->
      EConcat args ==> t1 -> EConcat args ==> t2 -> t1 = t2.
  Proof.
    intros ? ? ? He H H0. inv H. inv H0.
    assert (Heq: forall n t1 t2, nth_error ts n = Some t1 -> nth_error ts0 n = Some t2 ->
                            t1 = t2).
    - intros. assert (Hlt: n < length args).
      + rewrite H2. apply nth_error_Some. unfold not. intros.
        rewrite H in H5. discriminate.
      + assert (Hnth: exists e, nth_error args n = Some e).
        * exists (nth n args (EAtom 0)). apply nth_error_nth'. assumption.
        * destruct Hnth. apply (He _ _ H5); firstorder.
    - assert (Heql: ts = ts0).
      + apply nth_ext with (d := 0) (d' := 0). rewrite H2 in *. assumption.
        intros. apply Heq with (n := n). apply (nth_error_nth' _ _ H).
        rewrite <- H2 in H. rewrite H1 in H. apply (nth_error_nth' _ _ H).
      + subst. reflexivity.
  Qed.

  Lemma check_can_grow : forall e t s, e <== t -> t <= s -> e <== s.
  Proof.
    Ltac _check_can_grow_tac :=
      match goal with
      | [ HRes: Resizable _, H: ?e ==> ?x, Hle: ?x <= ?y |- ?e <== ?z ] =>
          apply (ResizeC HRes H); apply (le_trans x y z); assumption
      | [ H: _ <== _ |- _ <== _ ] => inv H; _check_can_grow_tac
      end
    .
    induction e using Expr_ind; intros; try _check_can_grow_tac.
    - inv H. inv H1. constructor. firstorder. firstorder.
    - inv H. inv H1. constructor. firstorder.
    - inv H. inv H1. assert (H : e1 <== s). firstorder. apply (ShiftC H H5).
    - inv H. inv H1. apply (CondC H4). firstorder. firstorder.
  Qed.

  Lemma check_grow_synth_and_synth_inj :
    forall e, (forall t s, e ==> t -> e <== s -> t <= s) /\ (forall t1 t2, e ==> t1 -> e ==> t2 -> t1 = t2).
  Proof.
    induction e using Expr_ind.
    - split; intros; inv H; inv H0; try (inv H1); firstorder.
    - split; intros.
      + inv H0. inv H1. inv H; firstorder.
      + inv H; inv H0; firstorder; apply le_antisymm; firstorder.
    - split; intros; inv H0; [inv H1 | inv H | inv H]; firstorder.
    - split; intros; inv H; inv H0; firstorder. inv H1.
      assert (Heq: t0 = s0). firstorder. subst. firstorder.
    - split; intros; inv H0; try (inv H2); inv H; firstorder.
    - split; intros; inv H0; try (inv H2); inv H; firstorder.
    - split; intros; inv H0; try (inv H2); inv H; firstorder.
    - split; intros; inv H0; [inv H1 | inv H | inv H]; firstorder.
    - split; intros; inv H0; try (inv H2); inv H; firstorder.
    - split; intros; inv H0; try (inv H2); inv H; firstorder.
    - split; intros; inv H0; try (inv H1); inv H; firstorder;
        apply le_antisymm; firstorder.
    - split; intros.
      + inv H1. assert (Heq: t0 = s0).
        { apply concat_args with (args := args); firstorder. } subst. firstorder.
      + apply concat_args with (args := args); firstorder.
    - split; intros; inv H0; try (inv H2); inv H; assert (Heq: te = te0); subst;
        firstorder.
    - split; intros; inv H0; inv H1; try (inv H2); firstorder.
  Qed.

  Theorem synth_inj : forall e t1 t2, e ==> t1 -> e ==> t2 -> t1 = t2.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e). apply (H2 _ _ H H0).
  Qed.

  Lemma synth_check_order : forall e t s, e ==> t -> e <== s -> t <= s.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e). apply (H1 _ _ H H0).
  Qed.

  Lemma synth_can_check : forall e t s, e ==> t -> t <= s -> e <== s.
  Proof.
    induction e using Expr_ind; intros;
      try (apply ResizeC with (s := t0); [constructor | assumption | assumption]).
    - inv H.
      + apply BinOpC. firstorder. apply check_can_grow with (t := t0); assumption.
      + apply BinOpC. apply check_can_grow with (t := t0); firstorder. firstorder.
    - inv H. constructor. firstorder.
    - inv H. assert (H: e1 <== s). firstorder. apply (ShiftC H H5).
    - inv H.
      + apply (CondC H4). firstorder. apply (check_can_grow H7 H0).
      + apply (CondC H4). apply (check_can_grow H6 H0). firstorder.
  Qed.


  Theorem synth_check : forall e t, e ==> t -> forall s, t <= s <-> e <== s.
  Proof.
    split; intros.
    - apply (synth_can_check H H0).
    - apply (synth_check_order H H0).
  Qed.

  Lemma synth_on_list : forall args,
      (forall n e, nth_error args n = Some e -> exists t, e ==> t) ->
      exists ts, (forall n e te, nth_error args n = Some e -> nth_error ts n = Some te <-> e ==> te)
            /\ length args = length ts.
  Proof.
    induction args.
    - exists []. split. intros. destruct n; inversion H0. reflexivity.
    - intros. destruct IHargs.
      + intros. apply H with (n := S n). assumption.
      + destruct (H 0 a). reflexivity. exists (x0 :: x). split.
        * intros. destruct n. inv H2. simpl. split. intros. inv H2. assumption.
          intros. f_equal. apply (synth_inj H1 H2). simpl in *. firstorder.
        * simpl. destruct H0. rewrite H2. reflexivity.
  Qed.

  Theorem always_synth : forall e, exists t, e ==> t.
  Proof.
    induction e using Expr_ind; intros.
    - exists o. constructor.
    - destruct IHe1 as [t1 H1]. destruct IHe2 as [t2 H2]. destruct (le_ge_dec t1 t2).
      + exists t2. apply (RBinOpS (synth_can_check H1 l) H2).
      + exists t1. apply (LBinOpS H1 (synth_can_check H2 g)).
    - destruct IHe as [t H]. exists t. constructor. assumption.
    - destruct IHe as [t H]. exists t. constructor. assumption.
    - exists 1. destruct IHe1 as [t1 H1]. destruct IHe2 as [t2 H2].
      destruct (le_ge_dec t1 t2).
      + apply (RCompS (synth_can_check H1 l) H2).
      + apply (LCompS H1 (synth_can_check H2 g)).
    - exists 1. destruct IHe1 as [t1 H1]. destruct IHe2 as [t2 H2]. apply (LogicS H1 H2).
    - exists 1. destruct IHe as [t H]. apply (RedS H).
    - destruct IHe1 as [t1 H1]. destruct IHe2 as [t2 H2]. exists t1. apply (ShiftS H1 H2).
    - destruct IHe as [t H]. exists op. destruct (le_gt_dec t op).
      + apply (LAssignS (synth_can_check H l)).
      + apply (RAssignS H g).
    - destruct IHe as [t H]. exists op. apply (ShiftAssignS _ H).
    - destruct IHe1 as [t1 H1]. destruct IHe2 as [t2 H2]. destruct IHe3 as [t3 H3].
      destruct (le_ge_dec t2 t3).
      + exists t3. apply (RCondS H1 (synth_can_check H2 l) H3).
      + exists t2. apply (LCondS H1 H2 (synth_can_check H3 g)).
    - destruct (synth_on_list _ H) as [ts [H1 H2]]. exists (sum ts).
      apply ConcatS with (ts := ts); firstorder.
    - destruct IHe as [t H]. exists (n * t). apply ReplS with (te := t); firstorder.
    - destruct (synth_on_list _ H) as [ts [H1 H2]]. destruct IHe as [te He]. exists 1.
      destruct (max_in_list te ts).
      + unfold max_list in H0. apply LInsideS with (t := te). assumption.
        intros. destruct (H _ _ H3) as [tes Hes]. apply (synth_can_check Hes). apply H0.
        apply In_iff_nth_error. exists n. apply (H1 _ _ _ H3). assumption.
      + destruct H0 as [m [H3 [H4 H5]]]. unfold max_list in H4.
        apply RInsideS with (t := m). destruct (In_nth_error _ _ H3) as [n Hx].
        assert (Hex: exists e0, nth_error args n = Some e0).
        * exists (nth n args (EAtom 0)). apply nth_error_nth'. rewrite H2.
          apply nth_error_Some. unfold not. intros. rewrite H0 in Hx. inversion Hx.
        * destruct Hex as [e0 He0]. exists e0. split. apply (nth_error_In _ _ He0).
          apply (H1 _ _ _ He0). assumption.
        * apply (synth_can_check He H5).
        * intros. destruct (H _ _ H0) as [te0 He0]. apply synth_can_check with (t := te0).
          assumption. apply H4. apply (H1 _ _ _ H0) in He0. apply (nth_error_In _ _ He0).
  Qed.

  Theorem synth_dec : forall e t, decidable (e ==> t).
  Proof.
    intros. unfold decidable. destruct (always_synth e) as [t H].
    destruct (eq_dec t0 t).
    - subst. left. assumption.
    - right. unfold not in *. intros. apply n. apply (synth_inj H0 H).
  Qed.

  Definition minimal (P : nat -> Prop) x := (forall u, P u -> x <= u) /\ P x.

  Theorem synth_minimal_check : forall e s, minimal (fun s => (forall t, s <= t -> e <== t)) s -> e ==> s.
  Proof.
    unfold minimal. intros. destruct always_synth with (e := e) as [x Hx].
    assert (Heq: s = x).
    - destruct H as [H1 H2]. apply le_antisymm.
      + apply H1. intros. apply synth_can_check with (t := x); firstorder.
      + apply synth_check_order with (e := e); firstorder.
    - subst. assumption.
  Qed.

End BiDir.
