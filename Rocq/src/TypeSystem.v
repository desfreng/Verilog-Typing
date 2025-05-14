From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Export Lia.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import Spec.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.

Import Expr.
Import ExprPath.
Import Path.
Import Spec.
Import Utils.

Set Implicit Arguments.

Module TypeSystem.

  Inductive Resizable : Expr -> Set :=
  | ResAtom : forall op, Resizable (EAtom op)
  | ResCast : forall e, Resizable (ECast e)
  | ResComp : forall lhs rhs, Resizable (EComp lhs rhs)
  | ResLogic : forall lhs rhs, Resizable (ELogic lhs rhs)
  | ResRed : forall e, Resizable (EReduction e)
  | ResAssign : forall lval arg, Resizable (EAssign lval arg)
  | ResShiftAssign : forall lval arg, Resizable (EShiftAssign lval arg)
  | ResConcat : forall args, Resizable (EConcat args)
  | ResRepl : forall amount arg, Resizable (ERepl amount arg)
  .

  Definition Initial t : path -> option nat :=
    fun p =>
      match p with
      | [] => Some t
      | _ :: _ => None
      end
  .

  Definition ReplaceRoot t (f: path -> option nat) : path -> option nat :=
    fun p =>
      match p with
      | [] => Some t
      | _ :: _ => f p
      end
  .

  Definition Binary t (f g: path -> option nat) : path -> option nat :=
    fun p =>
      match p with
      | [] => Some t
      | Left :: p => f p
      | Right :: p => g p
      | _ :: _ => None
      end
  .

  Definition Unary t (f: path -> option nat) : path -> option nat :=
    fun p =>
      match p with
      | [] => Some t
      | Arg :: p => f p
      | _ :: _ => None
      end
  .

  Definition Ternary t (f g h: path -> option nat) : path -> option nat :=
    fun p =>
      match p with
      | [] => Some t
      | Arg :: p => f p
      | Left :: p => g p
      | Right :: p => h p
      | _ :: _ => None
      end
  .

  Definition Narry t (f_k: list (path -> option nat)) : path -> option nat :=
    fun p => match p with
          | [] => Some t
          | Args i :: p => match nth_error f_k i with
                         | Some f => f p
                         | None => None
                         end
          | _ :: _ => None
          end
  .

  Reserved Notation "e '==>' t '-|' f" (at level 70).
  Reserved Notation "e '<==' t '-|' f" (at level 70).

  Inductive synth : Expr -> nat -> (path -> option nat) -> Prop :=
  | AtomS : forall op, EAtom op ==> op -| Initial op

  | LBinOpS : forall a b t fa fb,
      a ==> t -| fa ->
      b <== t -| fb ->
      EBinOp a b ==> t -| Binary t fa fb

  | RBinOpS : forall a b t fa fb,
      a <== t -| fa ->
      b ==> t -| fb ->
      EBinOp a b ==> t -| Binary t fa fb

  | UnOpS : forall e t f,
      e ==> t -| f ->
      EUnOp e ==> t -| Unary t f

  | CastS : forall e t f,
      e ==> t -| f ->
      ECast e ==> t -| Unary t f

  | LCompS : forall a b t fa fb,
      a ==> t -| fa ->
      b <== t -| fb ->
      EComp a b ==> 1 -| Binary 1 fa fb

  | RCompS : forall a b t fa fb,
      a <== t -| fa ->
      b ==> t -| fb ->
      EComp a b ==> 1 -| Binary 1 fa fb

  | LogicS : forall a b ta tb fa fb,
      a ==> ta -| fa ->
      b ==> tb -| fb ->
      ELogic a b ==> 1 -| Binary 1 fa fb

  | RedS : forall e t f,
      e ==> t -| f ->
      EReduction e ==> 1 -| Unary 1 f

  | ShiftS : forall a b t tb fa fb,
      a ==> t -| fa ->
      b ==> tb -| fb ->
      EShift a b ==> t -| Binary t fa fb

  | LAssignS : forall lval e f,
      e <== lval -| f ->
      EAssign lval e ==> lval -| Unary lval f

  | RAssignS : forall lval e te f,
      e ==> te -| f ->
      lval < te ->
      EAssign lval e ==> lval -| Unary lval f

  | ShiftAssignS : forall lval e te f,
      e ==> te -| f ->
      EShiftAssign lval e ==> lval -| Unary lval f

  | LCondS : forall e a b t te fe fa fb,
      e ==> te -| fe ->
      a ==> t -| fa ->
      b <== t -| fb ->
      ECond e a b ==> t -| Ternary t fe fa fb

  | RCondS : forall e a b t te fe fa fb,
      e ==> te -| fe ->
      a <== t -| fa ->
      b ==> t -| fb ->
      ECond e a b ==> t -| Ternary t fe fa fb

  | ConcatS : forall args ts t fs,
      length args = length ts ->
      length args = length fs ->
      (forall n e te fe, nth_error args n = Some e ->
                    nth_error ts n = Some te ->
                    nth_error fs n = Some fe ->
                    e ==> te -| fe) ->
      t = sum ts ->
      EConcat args ==> t -| Narry t fs

  | ReplS : forall i e te t f,
      e ==> te -| f ->
      t = i * te ->
      ERepl i e ==> t -| Unary t f

  where "e '==>' n '-|' f" := (synth e n f)

  with check : Expr -> nat -> (path -> option nat) -> Prop :=
  | ResizeC : forall e s t f,
      Resizable e ->
      e ==> s -| f ->
      s <= t ->
      e <== t -| ReplaceRoot t f

  | BinOpC : forall a b t fa fb,
      a <== t -| fa ->
      b <== t -| fb ->
      EBinOp a b <== t -| Binary t fa fb

  | UnOpC : forall e t f,
      e <== t -| f ->
      EUnOp e <== t -| Unary t f

  | ShiftC : forall a b t tb fa fb,
      a <== t -| fa ->
      b ==> tb -| fb ->
      EShift a b <== t -| Binary t fa fb

  | CondC : forall e a b t te fe fa fb,
      e ==> te -| fe ->
      a <== t -| fa ->
      b <== t -| fb ->
      ECond e a b <== t -| Ternary t fe fa fb

  where "e '<==' n '-|' f" := (check e n f)
  .


  Lemma synth_root : forall e t f, e ==> t -| f -> f [] = Some t.
  Proof.
    intros. inv H; reflexivity.
  Qed.

  Lemma check_root : forall e t f, e <== t -| f -> f [] = Some t.
  Proof.
    intros. inv H; reflexivity.
  Qed.

  Lemma concat_synth_inj_t: forall args f1 f2 t1 t2,
      (forall n e, nth_error args n = Some e -> forall t1 t2 f1 f2,
            e ==> t1 -| f1 -> e ==> t2 -| f2 -> t1 = t2) ->
      EConcat args ==> t1 -| f1 -> EConcat args ==> t2 -| f2 -> t1 = t2.
  Proof.
    intros ? ? ? ? ? He H H0. inv H. inv H0.
    assert (Heqt: forall n t1 t2,
               nth_error ts n = Some t1 -> nth_error ts0 n = Some t2 -> t1 = t2).
    - intros. repeat gen_nth. destruct (He _ _ H7 t1 t2 x1 x0); firstorder.
    - assert (Heql: ts = ts0). apply nth_ext with (d := 0) (d' := 0).
      rewrite H2 in *. assumption. intros. apply Heqt with (n := n).
      apply (nth_error_nth' _ _ H). rewrite <- H2 in H. rewrite H1 in H.
      apply (nth_error_nth' _ _ H). subst. reflexivity.
  Qed.

  Lemma concat_synth_inj_f: forall args t1 t2 f1 f2,
      (forall n e, nth_error args n = Some e -> forall t1 t2 f1 f2,
            e ==> t1 -| f1 -> e ==> t2 -| f2 -> t1 = t2 /\ forall p, f1 p = f2 p) ->
      EConcat args ==> t1 -| f1 -> EConcat args ==> t2 -| f2 -> forall p, f1 p = f2 p.
  Proof.
    intros ? ? ? ? ? He H H0. assert (Heq: t1 = t2).
    { eapply concat_synth_inj_t. intros. edestruct He.
      apply H1. apply H2. apply H3. assumption. eassumption. eassumption.
    } subst.
    inv H. inv H0. intros.
    assert (Heqf: forall n f1 f2, nth_error fs n = Some f1 -> nth_error fs0 n = Some f2 ->
                             forall p, f1 p = f2 p).
    { intros. repeat gen_nth. destruct (He _ _ H8 x2 x0 f1 f2); firstorder. }
    destruct p as [|[]]; try reflexivity. simpl. destruct (nth_error fs i) eqn:Hfs.
    - repeat gen_nth. rewrite H0. apply Heqf with (n := i); assumption.
    - destruct (nth_error fs0 i) eqn:Hfs0; try reflexivity. exfalso. repeat gen_nth.
      rewrite H1 in Hfs. discriminate Hfs.
  Qed.

  Lemma concat_synth_order_f: forall args t1 t2 f1 f2,
      (forall n e, nth_error args n = Some e -> forall t1 t2 f1 f2,
            e ==> t1 -| f1 -> e ==> t2 -| f2 ->
            t1 = t2 /\ forall p, le_option_nat (f1 p) (f2 p)) ->
      EConcat args ==> t1 -| f1 -> EConcat args ==> t2 -| f2 ->
      forall p, le_option_nat (f1 p) (f2 p).
  Proof.
    intros ? ? ? ? ? He H H0. assert (Heq: t1 = t2).
    { eapply concat_synth_inj_t. intros. edestruct He.
      apply H1. apply H2. apply H3. assumption. eassumption. eassumption.
    } subst.
    inv H. inv H0. intros.
    assert (Hltf: forall n f1 f2, nth_error fs n = Some f1 -> nth_error fs0 n = Some f2 ->
                             forall p, le_option_nat (f1 p) (f2 p)).
    { intros. repeat gen_nth. destruct (He _ _ H8 x2 x0 f1 f2); firstorder. }
    destruct p as [|[]]; try reflexivity. simpl. destruct (nth_error fs i) eqn:Hfs.
    - repeat gen_nth. rewrite H0. apply Hltf with (n := i); assumption.
    - destruct (nth_error fs0 i) eqn:Hfs0; try reflexivity.
  Qed.

  Theorem check_can_grow : forall e t f, e <== t -| f -> forall s, t <= s -> exists f', e <== s -| f'.
  Proof.
    Ltac _check_can_grow_tac :=
      match goal with
      | [ HRes: Resizable _, H: _ ==> ?x -| _, Hle: ?x <= ?y |- ?e <== ?z -| _ ] =>
          apply (ResizeC HRes H); apply (le_trans x y z); assumption
      | [ H: _ <== _ -| _ |- ex _ ] => inv H; eexists; _check_can_grow_tac
      end
    .
    induction e using Expr_ind; intros; try _check_can_grow_tac.
    - inv H. inv H1. edestruct IHe1; edestruct IHe2; try eassumption.
      eexists. constructor; eassumption.
    - inv H. inv H1. edestruct IHe; try eassumption. eexists. constructor. eassumption.
    - inv H. inv H1. edestruct IHe1; try eassumption. eexists. apply (ShiftC H H6).
    - inv H. inv H1. edestruct IHe2; edestruct IHe3; try eassumption.
      eexists. eapply (CondC H4); eassumption.
  Qed.

  Ltac inv_ts :=
    match goal with
    | [ H: _ _ ==> _ -| _ |- _ ] => inv H; try inv_ts
    | [ H: _ _ <== _ -| _ |- _ ] => inv H; try inv_ts
    | [ H: Resizable _ |- _ ] => inv H
    end
  .

  Lemma check_grow_synth_and_synth_inj :
    forall e, (forall t s f1 f2, e ==> t -| f1 -> e <== s -| f2 -> t <= s) /\
           (forall t1 t2 f1 f2, e ==> t1 -| f1 -> e ==> t2 -| f2 -> t1 = t2) /\
           (forall t f1 f2, e ==> t -| f1 -> e ==> t -| f2 -> forall p, f1 p = f2 p) /\
           (forall t f1 f2, e <== t -| f1 -> e <== t -| f2 -> forall p, f1 p = f2 p) /\
           (forall t f1 f2, e ==> t -| f1 -> e <== t -| f2 -> forall p, f1 p = f2 p) /\
           (forall t s f1 f2, e ==> t -| f1 -> e <== s -| f2 -> forall p, le_option_nat (f1 p) (f2 p)) /\
           (forall t s f1 f2, e <== t -| f1 -> e <== s -| f2 -> t <= s ->
                         forall p, le_option_nat (f1 p) (f2 p)).
  Proof.
    Ltac _eq_gen_inj :=
      match goal with
      | [ A: ?e ==> ?t -| _, B: ?e ==> ?s -| _, H: forall _ _ _ _, _ -> _ -> _ = _ |- _ ] =>
          let Heq := fresh in assert (Heq: t = s) by apply (H _ _ _ _ A B);
                              clear H; subst
      | [ A: ?e ==> ?t -| _, B: ?e <== ?s -| _, H: forall _ _ _ _, _ -> _ -> _ <= _ |- _ ] =>
          let Hlt := fresh in assert (Hlt: t <= s) by apply (H _ _ _ _ A B);
                              clear H; try _eq_gen_inj; try lia
      | [ H: ?a <= ?b, P: ?b <= ?a |- _ ] =>
          let Heq := fresh in assert (Heq: a = b) by apply (le_antisymm _ _ H P);
                              clear H; clear P; subst
      end
    .
    Ltac _tac_inj :=
      match goal with
      (* Values *)
      | [ |- _ = _ ] => _eq_gen_inj; auto
      | [  A: ?e ==> ?t -| _, B: ?e <== ?s -| _, H: forall _ _ _ _, _ -> _ -> _ <= _ |- ?t <= ?s ] =>
          apply (H _ _ _ _ A B)
      | [ A: ?e ==> ?t -| _, B: ?e ==> ?s -| _, H: forall _ _ _ _, _ -> _ -> _ = _ |- _ ] =>
          let Heq := fresh in assert (Heq: t = s) by apply (H _ _ _ _ A B);
                              clear H; subst; auto; _tac_inj
      (* Functions *)
      (* - Synth & Check *)
      | [  A: ?e ==> ?t -| _, B: ?e <== ?t -| _,
              H: forall _ _ _, _ -> _ -> forall _, _ =  _ |- _ _ = _ _ ] =>
          apply (H _ _ _ A B) || symmetry; apply (H _ _ _ A B)
      (* Both synth *)
      | [ A: ?e ==> ?t -| _, B: ?e ==> ?t -| _,
              H: forall _ _ _, _ -> _ -> forall _,  _ = _ |- _ _ = _ _ ] =>
          try _eq_gen_inj; apply (H _ _ _ A B)
        (* Both check *)
      | [ A: ?e <== ?t -| ?f1, B: ?e <== ?t -| ?f2,
              H: forall _ _ _, _ -> _ -> forall _, _ = _ |- ?f1 _ = ?f2 _ ] =>
          apply (H _ _ _ A B)
      | [ A: ?e ==> _ -| _, B: ?e <== _ -| _,
              H: forall _ _ _ _, _ -> _ -> forall _, le_option_nat _ _
                                         |- le_option_nat _ _ ] =>
          apply (H _ _ _ _ A B)
      | [ A: ?e <== ?t -| _, B: ?e <== ?s -| _, C: ?t <= ?s,
                H: forall _ _ _ _, _ -> _ -> _ -> forall _, le_option_nat _ _
                                               |- le_option_nat _ _ ] =>
          apply (H _ _ _ _ A B C)
      | [ A: ?e ==> ?t -| _, B: ?e ==> ?t -| _,
              H: forall _ _ _, _ -> _ -> forall _, _ = _ |- le_option_nat _ _ ] =>
          rewrite (H _ _ _ A B); reflexivity
      | [ A: ?e <== ?t -| _, B: ?e <== ?t -| _,
              H: forall _ _ _, _ -> _ -> forall _, _ = _ |- le_option_nat _ _ ] =>
          rewrite (H _ _ _ A B); reflexivity
      | [ A: ?e ==> ?t -| _, B: ?e <== ?t -| _,
              H: forall _ _ _, _ -> _ -> forall _, _ = _ |- le_option_nat _ _ ] =>
          rewrite (H _ _ _ A B); reflexivity
      end
    .
    induction e using Expr_ind; repeat splitAnd; intros; repeat splitHyp;
      try (destruct p as [|[]]);
      try (inv_ts; auto; repeat _tac_inj + inv_ts;
           simpl; try reflexivity; repeat _tac_inj + inv_ts;
           simpl; repeat _eq_gen_inj; auto; _tac_inj).
    - inv H1. assert (Heq: t0 = s0).
      { eapply (concat_synth_inj_t _ H0 H3). Unshelve.
        intros. destruct (H _ _ H1). repeat splitHyp. apply (H8 _ _ _ _ H5 H6).
      } subst. assumption.
    - eapply (concat_synth_inj_t _ H1 H2). Unshelve.
      intros. destruct (H _ _ H3). repeat splitHyp. apply (H7 _ _ _ _ H4 H5).
    - eapply (concat_synth_inj_f _ H2 H3). Unshelve.
      intros. destruct (H _ _ H4). repeat splitHyp. splitAnd. apply (H8 _ _ _ _ H5 H6).
      intros. subst. apply (H9 _ _ _ H5 H6).
    - inv H3. inv H4. assert (Heq: forall p, f p = f0 p).
      { eapply (concat_synth_inj_f _ H6 H8). Unshelve.
        intros. destruct (H _ _ H4). repeat splitHyp. splitAnd.
        apply (H13 _ _ _ _ H10 H11). intros. subst. apply (H14 _ _ _ H10 H11).
      } simpl. apply Heq.
    - inv H5. assert (Heq: forall p, f1 p = f p).
      { eapply (concat_synth_inj_f _ H4 H7). Unshelve.
        intros. destruct (H _ _ H5). repeat splitHyp. splitAnd.
        apply (H12 _ _ _ _ H9 H10). intros. subst. apply (H13 _ _ _ H9 H10).
      } simpl. apply Heq.
    - inv H6. _eq_gen_inj. simpl. rewrite (synth_root H5). trivial.
    - inv H6. _eq_gen_inj. simpl. eapply (concat_synth_order_f _ H5 H8).
      Unshelve. intros. destruct (H _ _ H1). repeat splitHyp. repeat splitAnd.
      apply (H12 _ _ _ _ H6 H10). subst. rewrite (H13 _ _ _ H6 H10). reflexivity.
    - inv H6. inv H7. _eq_gen_inj. simpl. eapply (concat_synth_order_f _ H10 H12).
      Unshelve. intros. destruct (H _ _ H1).
      repeat splitHyp. repeat splitAnd. apply (H16 _ _ _ _ H7 H14). subst.
      rewrite (H17 _ _ _ H7 H14). reflexivity.
  Qed.

  Theorem synth_check_order : forall e t s f1 f2, e ==> t -| f1 -> e <== s -| f2 -> t <= s.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e). apply (H1 _ _ _ _ H H0).
  Qed.

  Theorem synth_inj : forall e t1 t2 f1 f2, e ==> t1 -| f1 -> e ==> t2 -| f2 -> t1 = t2.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e).
    repeat splitHyp. apply (H2 _ _ _ _ H H0).
  Qed.

  Theorem synth_inj_f : forall e t1 t2 f1 f2, e ==> t1 -| f1 -> e ==> t2 -| f2 -> forall p, f1 p = f2 p.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e).
    repeat splitHyp. rewrite (H2 _ _ _ _ H H0) in H. apply (H3 _ _ _ H H0).
  Qed.

  Theorem synth_check_inj_f : forall e t f1 f2, e ==> t -| f1 -> e <== t -| f2 -> forall p, f1 p = f2 p.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e). firstorder.
  Qed.

  Theorem check_inj_f : forall e t f1 f2, e <== t -| f1 -> e <== t -| f2 -> forall p, f1 p = f2 p.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e). firstorder.
  Qed.

  Theorem synth_check_order_f : forall e t s f1 f2,
      e ==> t -| f1 -> e <== s -| f2 -> forall p n1 n2, f1 p = Some n1 -> f2 p = Some n2 -> n1 <= n2.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e). unfold le_option_nat in *.
    repeat splitHyp. apply (H8 _ _ _ _ H) with (p := p) in H0. rewrite H1 in H0.
    rewrite H2 in H0. assumption.
  Qed.

  Theorem check_order_f : forall e t s f1 f2,
      e <== t -| f1 -> e <== s -| f2 -> t <= s ->
      forall p n1 n2, f1 p = Some n1 -> f2 p = Some n2 -> n1 <= n2.
  Proof.
    intros. destruct (check_grow_synth_and_synth_inj e). unfold le_option_nat in *.
    repeat splitHyp. apply (H10 _ _ _ _ H H0) with (p := p) in H1. rewrite H2 in H1.
    rewrite H3 in H1. assumption.
  Qed.

  Lemma synth_can_check : forall e t s f, e ==> t -| f -> t <= s -> exists g, e <== s -| g.
  Proof.
    induction e using Expr_ind; intros; try (eexists; apply ResizeC with (s := t0);
                                             [constructor | eassumption | assumption]).
    - inv H.
      + destruct (IHe1 _ _ _ H3 H0). destruct (check_can_grow H6 H0).
        eexists. apply BinOpC; eassumption.
      + destruct (IHe2 _ _ _ H6 H0). destruct (check_can_grow H3 H0).
        eexists. apply BinOpC; eassumption.
    - inv H. destruct (IHe _ _ _ H2 H0). eexists. constructor. eassumption.
    - inv H. destruct (IHe1 _ _ _ H3 H0). eexists. apply (ShiftC H H6).
    - inv H.
      + destruct (IHe2 _ _ _ H7 H0). destruct (check_can_grow H8 H0).
        eexists. apply (CondC H4 H H1).
      + destruct (IHe3 _ _ _ H8 H0). destruct (check_can_grow H7 H0).
        eexists. apply (CondC H4 H1 H).
  Qed.

  Theorem synth_check : forall e t f, e ==> t -| f -> forall s, t <= s <-> exists g, e <== s -| g.
  Proof.
    split; intros.
    - apply (synth_can_check H H0).
    - destruct H0. apply (synth_check_order H H0).
  Qed.

  Lemma func_on_path : forall e,
      (forall t f, e ==> t -| f -> forall p, IsPath e p <-> exists n, f p = Some n) /\
        (forall t f, e <== t -| f -> forall p, IsPath e p <-> exists n, f p = Some n).
  Proof.
    Ltac _invHyp_fun_path :=
      match goal with
      | [ H: IsPath (_ _) _ |- _ ] => inv H
      | [ H: ex _ |- _ ] => inv H
      end
    .
    Ltac _tac_fun_path :=
      match goal with
      | [ H1: _ ==> _ -| _, H2: forall _ _, _ ==> _ -| _ -> _  |- _ ] =>
        try constructor; rewrite (H2 _ _ H1); eexists; eassumption
      | [ H1: _ <== _ -| _, H2: forall _ _, _ <== _ -| _ -> _  |- _ ] =>
          try constructor; rewrite (H2 _ _ H1); eexists; eassumption
      | [ |- IsPath _ [] ] => constructor
      end
    .
    induction e using Expr_ind; repeat split; intros; repeat splitHyp;
      inv_ts; repeat _invHyp_fun_path; try (try (eexists; reflexivity); firstorder);
      try (destruct p as [|[]]; simpl in *; discriminate H || inv H; _tac_fun_path).
    - destruct (H _ _ H2). repeat gen_nth. simpl. rewrite H7.
      assert (He: e ==> x0 -| x) by apply (H5 _ _ _ _ H2 H4 H7). firstorder.
    - destruct p as [|[]]; simpl in *; discriminate H0 || inv H0. constructor.
      destruct (nth_error fs i) eqn:Hnth. repeat gen_nth. econstructor. eassumption.
      destruct (H _ _ H0). apply (H5 _ _ _ _ H0 H1) in Hnth. _tac_fun_path.
      discriminate H2.
    - destruct (H _ _ H2). repeat gen_nth. simpl. rewrite H8.
      assert (He: e ==> x0 -| x) by apply (H7 _ _ _ _ H2 H6 H8). firstorder.
    - destruct p as [|[]]; simpl in *; discriminate H0 || inv H0. constructor.
      destruct (nth_error fs i) eqn:Hnth. repeat gen_nth. econstructor. eassumption.
      destruct (H _ _ H0). apply (H7 _ _ _ _ H0 H1) in Hnth. _tac_fun_path.
      discriminate H2.
  Qed.


  Theorem synth_f_path : forall e t f, e ==> t -| f -> forall p, IsPath e p <-> exists n, f p = Some n.
  Proof.
    intros e. destruct (func_on_path e). assumption.
  Qed.


  Theorem check_f_path : forall e t f, e <== t -| f -> forall p, IsPath e p <-> exists n, f p = Some n.
  Proof.
    intros e. destruct (func_on_path e). assumption.
  Qed.

  Lemma f_sub_exp : forall e,
      (forall t f, e ==> t -| f -> forall p e', e @[p] = Some e' ->
                                  exists t' f', (e' ==> t' -| f' \/ e' <== t' -| f') /\
                                             forall k, f (p ++ k) = f' k) /\
        (forall t f, e <== t -| f -> forall p e', e @[p] = Some e' ->
                                    exists t' f', (e' ==> t' -| f' \/ e' <== t' -| f') /\
                                               forall k, f (p ++ k) = f' k).
  Proof.
    Ltac _inv_se_f :=
      match goal with
      | [ H: _ _ @[ _ ] = _ |- _ ] => inv H
      end
    .
    induction e using Expr_ind; split; intros; repeat splitHyp;
      destruct p as [|[]]; _inv_se_f; try (exists t0; exists f; split; auto; intros; reflexivity);
      repeat inv_ts; firstorder.
    - destruct (nth_error args i) eqn:Hnth; try (discriminate H3). destruct (H _ _ Hnth).
      clear H. repeat inv_ts. repeat gen_nth. simpl. rewrite H.
      assert (He: e ==> x0 -| x) by apply (H5 _ _ _ _ Hnth H4 H).
      firstorder.
    - destruct (nth_error args i) eqn:Hnth; try (discriminate H3). destruct (H _ _ Hnth).
      clear H. repeat inv_ts. repeat gen_nth. simpl. rewrite H.
      assert (He: e ==> x0 -| x) by apply (H7 _ _ _ _ Hnth H2 H).
      firstorder.
  Qed.

  Theorem synth_sub_expr : forall e t f p e',
      e ==> t -| f ->  e @[p] = Some e' ->
      exists t' f', (e' ==> t' -| f' \/ e' <== t' -| f') /\ forall k, f (p ++ k) = f' k.
  Proof.
    intros. destruct (f_sub_exp e). firstorder.
  Qed.

  Theorem check_sub_expr : forall e t f p e',
      e <== t -| f ->  e @[p] = Some e' ->
      exists t' f', (e' ==> t' -| f' \/ e' <== t' -| f') /\ forall k, f (p ++ k) = f' k.
  Proof.
    intros. destruct (f_sub_exp e). firstorder.
  Qed.

  Theorem synth_determine : forall e, exists f, e ==> determine e -| f.
  Proof.
    induction e using Expr_ind; repeat existsHyp.
    - eexists. constructor.
    - destruct (max_dec_bis (determine e1) (determine e2)) as [[H1 H2]|[H1 H2]].
      + destruct (synth_can_check H H2). eexists. simpl. rewrite H1.
        constructor; eassumption.
      + destruct (synth_can_check H0 H2). eexists. simpl. rewrite H1.
        constructor; eassumption.
    - eexists. constructor. eassumption.
    - eexists. constructor. eassumption.
    - destruct (max_dec_bis (determine e1) (determine e2)) as [[H1 H2]|[H1 H2]].
      + destruct (synth_can_check H H2). eexists. simpl. eapply LCompS; eassumption.
      + destruct (synth_can_check H0 H2). eexists. simpl. eapply RCompS; eassumption.
    - eexists. eapply LogicS; eassumption.
    - eexists. eapply RedS; eassumption.
    - eexists. eapply ShiftS; eassumption.
    - destruct (le_gt_dec (determine e) op).
      + destruct (synth_can_check H l). eexists. eapply LAssignS; eassumption.
      + eexists. eapply RAssignS; eassumption.
    - eexists. eapply ShiftAssignS; eassumption.
    - destruct (max_dec_bis (determine e2) (determine e3)) as [[H2 H3]|[H2 H3]].
      + destruct (synth_can_check H H3). eexists. simpl. rewrite H2.
        eapply LCondS; eassumption.
      + destruct (synth_can_check H0 H3). eexists. simpl. rewrite H2.
        eapply RCondS; eassumption.
    - assert (Hfs: exists fs, length fs = length args /\ forall n e t f,
                   nth_error args n = Some e ->
                   nth_error (map determine args) n = Some t ->
                   nth_error fs n = Some f -> e ==> t -| f).
      + induction args.
        * eexists []. split. reflexivity. intros []; intros; discriminate H0.
        * edestruct IHargs. intros. destruct (H (S n) e H0). exists x. assumption.
          destruct H0. destruct (H 0 a). reflexivity. exists (x0 :: x). split.
          -- simpl. rewrite H0. reflexivity.
          -- intros. destruct n. inv H3. inv H4. inv H5. assumption.
             simpl in *. firstorder.
      + destruct Hfs as [fs [H1 H2]]. eexists.
        apply ConcatS with (ts := map determine args).
        * symmetry. apply length_map.
        * symmetry. eassumption.
        * assumption.
        * reflexivity.
    - eexists. eapply ReplS. eassumption. reflexivity.
  Qed.

  Theorem always_synth : forall e, exists t f, e ==> t -| f.
  Proof.
    intros. exists (determine e). destruct (synth_determine e) as [f H]. exists f. assumption.
  Qed.

  Theorem always_check : forall e, exists t f, e <== t -| f.
  Proof.
    intros. exists (determine e). destruct (synth_determine e) as [f H].
    apply (synth_can_check H (le_refl _)).
  Qed.

  Theorem synth_must_be_determine : forall e t f,
      e ==> t -| f -> t = determine e /\ f [] = Some (determine e).
  Proof.
    intros. splitAnd.
    - destruct (synth_determine e). apply (synth_inj H H0).
    - rewrite (synth_root H). subst. reflexivity.
  Qed.

  Definition P e s := forall t, s <= t -> exists g, e <== t -| g.

  Theorem synth_minimal_check : forall e s, P e s -> (forall u, P e u -> s <= u) -> exists f, e ==> s -| f.
  Proof.
    unfold P. intros. destruct synth_determine with (e := e) as [x Hx].
    assert (Heq: s = determine e).
    { apply le_antisymm.
      - apply H0. intros. apply (synth_can_check Hx H1).
      - destruct (H s). reflexivity. apply (synth_check_order Hx H1).
    } subst. exists x. assumption.
  Qed.

  Lemma synth_check_determine_order : forall e1 e2 t1 t2 f1 f2,
      e1 ==> t1 -| f1 -> e2 <== t2 -| f2 -> t2 <= t1 -> determine e2 <= determine e1.
  Proof.
    intros. destruct (synth_must_be_determine H) as [Ht Hf].
    subst. destruct (synth_determine e2).
    apply (synth_check_order H2) in H0. apply (le_trans _ _ _ H0 H1).
  Qed.

  Lemma synth_and_order : forall e f t,
      e <== t -| f -> t <= determine e -> determine e = t.
  Proof.
    intros.
    apply le_antisymm.
    - destruct (always_synth e) as [t1 [f1 H1]]. destruct (synth_must_be_determine H1).
      subst. apply (synth_check_order H1 H).
    - assumption.
  Qed.

End TypeSystem.
