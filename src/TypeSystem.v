From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Export Lia.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.

Import Expr.
Import ExprPath.
Import Path.
Import Utils.


(** * Typing system definition *)
(** In this module, we define our typing system and prove some of its properties. *)
Module TypeSystem.

  (** Definition of resizable expressions. *)
  Variant Resizable : Expr -> Set :=
  | ResAtom : forall op, Resizable (EOperand op)
  | ResComp : forall lhs rhs, Resizable (EComp lhs rhs)
  | ResLogic : forall lhs rhs, Resizable (ELogic lhs rhs)
  | ResRed : forall e, Resizable (EReduction e)
  | ResAssign : forall lval arg, Resizable (EAssign lval arg)
  | ResConcat : forall args, Resizable (EConcat args)
  | ResRepl : forall amount arg, Resizable (ERepl amount arg)
  .


  (** ** Functions Combinators *)
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
      | 0 :: p => f p
      | 1 :: p => g p
      | _ :: _ => None
      end
  .

  Definition Unary t (f: path -> option nat) : path -> option nat :=
    fun p =>
      match p with
      | [] => Some t
      | 0 :: p => f p
      | _ :: _ => None
      end
  .

  Definition Ternary t (f g h: path -> option nat) : path -> option nat :=
    fun p =>
      match p with
      | [] => Some t
      | 0 :: p => f p
      | 1 :: p => g p
      | 2 :: p => h p
      | _ :: _ => None
      end
  .

  Definition Nary t (f_k: list (path -> option nat)) : path -> option nat :=
    fun p => match p with
          | [] => Some t
          | i :: p => match nth_error f_k i with
                         | Some f => f p
                         | None => None
                         end
          end
  .

  Reserved Notation "e '==>' t '-|' f" (at level 70).
  Reserved Notation "e '<==' t '-|' f" (at level 70).

  Inductive synth : Expr -> nat -> (path -> option nat) -> Prop :=
  | AtomS : forall op f,
      f = Initial op ->
      EOperand op ==> op -| f

  | LBinOpS : forall a b t f fa fb,
      a ==> t -| fa ->
      b <== t -| fb ->
      f = Binary t fa fb ->
      EBinOp a b ==> t -| f

  | RBinOpS : forall a b t f fa fb,
      a <== t -| fa ->
      b ==> t -| fb ->
      f = Binary t fa fb ->
      EBinOp a b ==> t -| f

  | UnOpS : forall e t f fe,
      e ==> t -| fe ->
      f = Unary t fe ->
      EUnOp e ==> t -| f

  | LCompS : forall a b t f fa fb,
      a ==> t -| fa ->
      b <== t -| fb ->
      f = Binary 1 fa fb ->
      EComp a b ==> 1 -| f

  | RCompS : forall a b t f fa fb,
      a <== t -| fa ->
      b ==> t -| fb ->
      f = Binary 1 fa fb ->
      EComp a b ==> 1 -| f

  | LogicS : forall a b f ta tb fa fb,
      a ==> ta -| fa ->
      b ==> tb -| fb ->
      f = Binary 1 fa fb ->
      ELogic a b ==> 1 -| f

  | RedS : forall e t f fe,
      e ==> t -| fe ->
      f = Unary 1 fe ->
      EReduction e ==> 1 -| f

  | ShiftS : forall a b t f tb fa fb,
      a ==> t -| fa ->
      b ==> tb -| fb ->
      f = Binary t fa fb ->
      EShift a b ==> t -| f

  | LAssignS : forall lval e f fe,
      e <== lval -| fe ->
      f = Unary lval fe ->
      EAssign lval e ==> lval -| f

  | RAssignS : forall lval e f te fe,
      e ==> te -| fe ->
      lval < te ->
      f = Unary lval fe ->
      EAssign lval e ==> lval -| f

  | LCondS : forall e a b t f te fe fa fb,
      e ==> te -| fe ->
      a ==> t -| fa ->
      b <== t -| fb ->
      f = Ternary t fe fa fb ->
      ECond e a b ==> t -| f

  | RCondS : forall e a b t f te fe fa fb,
      e ==> te -| fe ->
      a <== t -| fa ->
      b ==> t -| fb ->
      f = Ternary t fe fa fb ->
      ECond e a b ==> t -| f

  | ConcatS : forall args t f ts fs,
      length args = length ts ->
      length args = length fs ->
      (forall n e te fe, nth_error args n = Some e ->
                    nth_error ts n = Some te ->
                    nth_error fs n = Some fe ->
                    e ==> te -| fe) ->
      t = sum ts ->
      f = Nary t fs ->
      EConcat args ==> t -| f

  | ReplS : forall i e t f te fe,
      e ==> te -| fe ->
      t = i * te ->
      f = Unary t fe ->
      ERepl i e ==> t -| f

  where "e '==>' n '-|' f" := (synth e n f)

  with check : Expr -> nat -> (path -> option nat) -> Prop :=
  | ResizeC : forall e t f s fe,
      Resizable e ->
      e ==> s -| fe ->
      s <= t ->
      f = ReplaceRoot t fe ->
      e <== t -| f

  | BinOpC : forall a b t f fa fb,
      a <== t -| fa ->
      b <== t -| fb ->
      f = Binary t fa fb ->
      EBinOp a b <== t -| f

  | UnOpC : forall e t f fe,
      e <== t -| fe ->
      f = Unary t fe ->
      EUnOp e <== t -| f

  | ShiftC : forall a b t f tb fa fb,
      a <== t -| fa ->
      b ==> tb -| fb ->
      f = Binary t fa fb ->
      EShift a b <== t -| f

  | CondC : forall e a b t f te fe fa fb,
      e ==> te -| fe ->
      a <== t -| fa ->
      b <== t -| fb ->
      f = Ternary t fe fa fb ->
      ECond e a b <== t -| f

  where "e '<==' n '-|' f" := (check e n f)
  .

  Ltac inv_ts :=
    match goal with
    | [ H: _ _ ==> _ -| _ |- _ ] => inv H; try inv_ts
    | [ H: _ _ <== _ -| _ |- _ ] => inv H; try inv_ts
    | [ H: Resizable _ |- _ ] => inv H
    end
  .

  Lemma synth_root : forall e t f, e ==> t -| f -> f [] = Some t.
  Proof.
    intros. inv H; reflexivity.
  Qed.

  Lemma check_root : forall e t f, e <== t -| f -> f [] = Some t.
  Proof.
    intros. inv H; reflexivity.
  Qed.

  Definition concat_inj_hyp args :=
    forall (n : nat) (e : Expr),
      nth_error args n = Some e ->
      forall (t1 t2 : nat) (f1 f2 : path -> option nat),
        e ==> t1 -| f1 ->
        e ==> t2 -| f2 ->
        t1 = t2 /\ (forall p : path, f1 p = f2 p).

  Lemma concat_synth_inj_t: forall args f1 f2 t1 t2,
      concat_inj_hyp args -> EConcat args ==> t1 -| f1 -> EConcat args ==> t2 -| f2 ->
      t1 = t2.
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
      concat_inj_hyp args -> EConcat args ==> t1 -| f1 -> EConcat args ==> t2 -| f2 ->
      forall p, f1 p = f2 p.
  Proof.
    intros ? ? ? ? ? He H H0.
    assert (Heq: t1 = t2) by apply (concat_synth_inj_t _ _ _ _ _ He H H0).
    inv H. inv H0. intros.
    assert (Heqf: forall n f1 f2, nth_error fs n = Some f1 -> nth_error fs0 n = Some f2 ->
                             forall p, f1 p = f2 p).
    { intros. repeat gen_nth. destruct (He _ _ H8 x2 x0 f1 f2); firstorder. }
    destruct p; try reflexivity. simpl. destruct (nth_error fs n) eqn:Hfs.
    - repeat gen_nth. rewrite H0. apply Heqf with (n := n); assumption.
    - destruct (nth_error fs0 n) eqn:Hfs0; try reflexivity. exfalso. repeat gen_nth.
      rewrite H1 in Hfs. discriminate Hfs.
  Qed.

  Lemma concat_synth_order_f: forall args t1 t2 f1 f2,
      concat_inj_hyp args -> EConcat args ==> t1 -| f1 -> EConcat args ==> t2 -| f2 ->
      forall p, le_option_nat (f1 p) (f2 p).
  Proof.
    intros ? ? ? ? ? He H H0 p.
    assert (Heq: forall p, f1 p = f2 p) by apply (concat_synth_inj_f _ _ _ _ _ He H H0).
    rewrite Heq. reflexivity.
  Qed.

  Theorem check_can_grow : forall e t f, e <== t -| f -> forall s, t <= s -> exists f', e <== s -| f'.
  Proof.
    Ltac _check_can_grow_tac :=
      match goal with
      | [ HRes: Resizable _, H: _ ==> ?x -| _, Hle: ?x <= ?y |- ?e <== ?z -| _ ] =>
          apply (ResizeC _ _ _ _ _ HRes H); try reflexivity;
          apply (le_trans x y z); eassumption
      | [ H: _ <== _ -| _ |- ex _ ] => inv H; eexists; _check_can_grow_tac
      end
    .
    induction e using Expr_ind; intros; try _check_can_grow_tac.
    - inv H. inv H1. edestruct IHe1; edestruct IHe2; try eassumption.
      eexists. econstructor; eassumption || reflexivity.
    - inv H. inv H1. edestruct IHe; try eassumption. eexists.
      econstructor; eassumption || reflexivity.
    - inv H. inv H1. edestruct IHe1; try eassumption. eexists.
      apply (ShiftC _ _ _ _ _ _ _ H H4). reflexivity.
    - inv H. inv H1. edestruct IHe2; edestruct IHe3; try eassumption.
      eexists. eapply (CondC _ _ _ _ _ _ _ _ _ H4); eassumption || reflexivity.
  Qed.

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
      | [ H: forall _ _, nth_error _ _ = Some _ -> _, G: nth_error _ _ = Some _ |- _ ] =>
          specialize (H _ _ G); repeat splitHyp; split; intros
      end
    .
    induction e using Expr_ind; repeat splitAnd; intros; repeat splitHyp;
    try (try (destruct p as [|[|[|[]]]]); inv_ts; simpl; repeat _eq_gen_inj;
         auto; try reflexivity; repeat _tac_inj; fail);
    assert (concat_inj_hyp args) by (unfold concat_inj_hyp; intros; repeat _tac_inj).
    - inv H1. assert _ by apply (concat_synth_inj_t _ _ _ _ _ H2 H0 H4).
      subst. assumption.
    - apply (concat_synth_inj_t _ _ _ _ _ H3 H1 H2).
    - apply (concat_synth_inj_f _ _ _ _ _ H4 H2 H3).
    - inv H3. inv H4. destruct p; simpl.
      + reflexivity.
      + apply (concat_synth_inj_f _ _ _ _ _ H5 H7 H9).
    - inv H5. destruct p; simpl.
      + apply (synth_root _ _ _ H4).
      + apply (concat_synth_inj_f _ _ _ _ _ H6 H4 H8).
    - inv H6. _eq_gen_inj. simpl. destruct p.
      + rewrite (synth_root _ _ _ H5). trivial.
      + apply (concat_synth_order_f _ _ _ _ _ H7 H5 H9).
    - inv H6. inv H7. _eq_gen_inj. simpl. destruct p.
      + assumption.
      + apply (concat_synth_order_f _ _ _ _ _ H9 H11 H13).
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
    induction e using Expr_ind; intros;
      try (eexists; eapply ResizeC with (s := t0);
           [constructor | eassumption | assumption | reflexivity]).
    - inv H.
      + destruct (IHe1 _ _ _ H3 H0). destruct (check_can_grow _ _ _ H4 _ H0).
        eexists. eapply BinOpC; eassumption || reflexivity.
      + destruct (IHe2 _ _ _ H4 H0). destruct (check_can_grow _ _ _ H3 _ H0).
        eexists. eapply BinOpC; eassumption || reflexivity.
    - inv H. destruct (IHe _ _ _ H2 H0). eexists.
      econstructor; eassumption || reflexivity.
    - inv H. destruct (IHe1 _ _ _ H3 H0). eexists. apply (ShiftC _ _ _ _ _ _ _ H H4).
      reflexivity.
    - inv H.
      + destruct (IHe2 _ _ _ H5 H0). destruct (check_can_grow _ _ _ H8 _ H0).
        eexists. apply (CondC _ _ _ _ _ _ _ _ _ H4 H H1). reflexivity.
      + destruct (IHe3 _ _ _ H8 H0). destruct (check_can_grow _ _ _ H5 _ H0).
        eexists. apply (CondC _ _ _ _ _ _ _ _ _ H4 H1 H). reflexivity.
  Qed.

  Theorem synth_check : forall e t f, e ==> t -| f -> forall s, t <= s <-> exists g, e <== s -| g.
  Proof.
    split; intros.
    - apply (synth_can_check _ _ _ _ H H0).
    - destruct H0. apply (synth_check_order _ _ _ _ _ H H0).
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
      try (destruct p as [|[|[|[]]]]; simpl in *; discriminate H || inv H;
           _tac_fun_path).
    - destruct (H _ _ H2). repeat gen_nth. simpl. rewrite H7.
      assert (He: e ==> x0 -| x) by apply (H5 _ _ _ _ H2 H4 H7). firstorder.
    - destruct p; simpl in *; discriminate H0 || inv H0. constructor.
      destruct (nth_error fs n) eqn:Hnth. repeat gen_nth. econstructor. eassumption.
      destruct (H _ _ H0). apply (H5 _ _ _ _ H0 H1) in Hnth. _tac_fun_path.
      discriminate H2.
    - destruct (H _ _ H2). repeat gen_nth. simpl. rewrite H8.
      assert (He: e ==> x0 -| x) by apply (H7 _ _ _ _ H2 H6 H8). firstorder.
    - destruct p; simpl in *; discriminate H0 || inv H0. constructor.
      destruct (nth_error fs n) eqn:Hnth. repeat gen_nth. econstructor. eassumption.
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
      try (destruct p as [|[|[|[]]]]; _inv_se_f;
           try (exists t0; exists f; split; auto; intros; reflexivity);
           repeat inv_ts; firstorder; fail).
    - destruct p; _inv_se_f.
      + exists t0; exists f; split; auto; intros; reflexivity.
      + destruct (nth_error args n) eqn:Hnth; try congruence.
        specialize (H _ _ Hnth). destruct H as [Hs Hc].
        repeat inv_ts. repeat gen_nth. specialize (H4 _ _ _ _ Hnth H0 H).
        simpl. rewrite H. firstorder.
    - destruct p; _inv_se_f.
      + exists t0; exists f; split; auto; intros; reflexivity.
      + destruct (nth_error args n) eqn:Hnth; try congruence.
        specialize (H _ _ Hnth). destruct H as [Hs Hc].
        repeat inv_ts. repeat gen_nth. specialize (H6 _ _ _ _ Hnth H0 H).
        simpl. rewrite H. firstorder.
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

  Theorem always_synth : forall e, exists t f, e ==> t -| f.
  Proof.
    induction e using Expr_ind; repeat existsHyp;
      try (eexists; eexists; econstructor; eassumption || reflexivity).
    - destruct (max_dec_bis x1 x) as [[H1 H2]|[H1 H2]].
      + destruct (synth_can_check _ _ _ _ H H2).
        eexists; eexists; econstructor; eassumption || reflexivity.
      + destruct (synth_can_check _ _ _ _ H0 H2).
        eexists; eexists; econstructor; eassumption || reflexivity.
    - destruct (max_dec_bis x1 x) as [[H1 H2]|[H1 H2]].
      + destruct (synth_can_check _ _ _ _ H H2).
        eexists; eexists; econstructor; eassumption || reflexivity.
      + destruct (synth_can_check _ _ _ _ H0 H2).
        eexists; eexists; econstructor; eassumption || reflexivity.
    - destruct (le_gt_dec x op).
      + destruct (synth_can_check _ _ _ _ H l).
        eexists; eexists; econstructor; eassumption || reflexivity.
      + eexists; eexists; econstructor; eassumption || reflexivity.
    - destruct (max_dec_bis x1 x) as [[H2 H3]|[H2 H3]].
      + destruct (synth_can_check _ _ _ _ H H3).
        eexists; eexists; econstructor; eassumption || reflexivity.
      + destruct (synth_can_check _ _ _ _ H0 H3).
        eexists; eexists; econstructor; eassumption || reflexivity.
    - assert (Hfs: exists ts, exists fs, length args = length ts /\
                                 length args = length fs /\ forall n e t f,
                   nth_error args n = Some e ->
                   nth_error ts n = Some t ->
                   nth_error fs n = Some f -> e ==> t -| f).
      + induction args.
        * exists []. exists []. repeat split. intros []; intros; discriminate H0.
        * destruct IHargs. intros. apply (H (S n) e H0). existsHyp.
          repeat splitHyp. destruct (H 0 a (Logic.eq_refl _)) as [t [f ?H]] .
          exists (t :: x). exists (f :: x0). repeat split; simpl; try congruence.
          intros. destruct n.
          -- inv H4. inv H5. inv H6. assumption.
          -- simpl in *. firstorder.
      + destruct Hfs as [ts [fs [H1 [H2 H3]]]].
        eexists; eexists; econstructor; eassumption || reflexivity.
  Qed.

  Theorem always_check : forall e, exists t f, e <== t -| f.
  Proof.
    intros. destruct (always_synth e) as [t [f H]]. exists t.
    apply (synth_can_check _ _ _ _ H (le_refl _)).
  Qed.

  Definition P e s := forall t, s <= t -> exists g, e <== t -| g.

  Theorem synth_minimal_check : forall e s, P e s -> (forall u, P e u -> s <= u) -> exists f, e ==> s -| f.
  Proof.
    unfold P. intros. destruct always_synth with (e := e) as [t [f Hx]].
    assert (Heq: s = t).
    { apply le_antisymm.
      - apply H0. intros. rewrite <- synth_check; eassumption.
      - destruct (H s). reflexivity.
        rewrite synth_check; try eexists; eassumption.
    } subst. exists f. assumption.
  Qed.
End TypeSystem.
