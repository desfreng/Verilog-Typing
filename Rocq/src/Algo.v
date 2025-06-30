From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import TypedExpr.
From Verilog Require Import TypedExprPath.
From Verilog Require Import TypeSystem.
From Verilog Require Import Spec.
From Verilog Require Import Utils.

Import Nat.
Import ListNotations.

Import Path.
Import Expr.
Import ExprPath.
Import TypedExpr.
Import TypedExprPath.
Import TypeSystem.
Import Spec.
Import Utils.
Import Learn.

Module Algo.
  Fixpoint down s e :=
    match e with
    | TAtom _ op => TAtom s op
    | TBinOp _ tLhs tRhs => TBinOp s (down s tLhs) (down s tRhs)
    | TUnOp _ tArg => TUnOp s (down s tArg)
    | TCast _ tArg => TCast s (down (size tArg) tArg)
    | TComp _ tLhs tRhs =>
        let sArg := max (size tLhs) (size tRhs) in
        TComp s (down sArg tLhs) (down sArg tRhs)
    | TLogic _ tLhs tRhs => TLogic s (down (size tLhs) tLhs) (down (size tRhs) tRhs)
    | TReduction _ tArg => TReduction s (down (size tArg) tArg)
    | TShift _ tLhs tRhs => TShift s (down s tLhs) (down (size tRhs) tRhs)
    | TAssign _ lval tArg =>
        let sArg := max lval (size tArg) in
        TAssign s lval (down sArg tArg)
    | TCond _ tArg tLhs tRhs => TCond s (down (size tArg) tArg) (down s tLhs) (down s tRhs)
    | TConcat _ tArgs =>
        TConcat s (map (fun tE => down (size tE) tE) tArgs)
    | TRepl _ n tArg => TRepl s n (down (size tArg) tArg)
    end
  .

  Fixpoint up e :=
    match e with
    | EAtom op => TAtom op op
    | EBinOp lhs rhs =>
        let uLhs := up lhs in
        let uRhs := up rhs in
        let s := max (size uLhs) (size uRhs) in
        TBinOp s uLhs uRhs
    | EUnOp arg =>
        let uArg := up arg in
        TUnOp (size uArg) uArg
    | ECast arg =>
        let uArg := up arg in
        TCast (size uArg) uArg
    | EComp lhs rhs =>
        let uLhs := up lhs in
        let uRhs := up rhs in
        TComp 1 uLhs uRhs
    | ELogic lhs rhs =>
        let uLhs := up lhs in
        let uRhs := up rhs in
        TLogic 1 uLhs uRhs
    | EReduction arg =>
        let uArg := up arg in
        TReduction 1 uArg
    | EShift lhs rhs =>
        let uLhs := up lhs in
        let uRhs := up rhs in
        TShift (size uLhs) uLhs uRhs
    | EAssign lval arg =>
        let uArg := up arg in
        TAssign lval lval uArg
    | ECond arg lhs rhs =>
        let uArg := up arg in
        let uLhs := up lhs in
        let uRhs := up rhs in
        let s := max (size uLhs) (size uRhs) in
        TCond s uArg uLhs uRhs
    | EConcat args =>
        let uArgs := map up args in
        let s := sum (map size uArgs) in
        TConcat s uArgs
    | ERepl n arg =>
        let uArg := up arg in
        TReduction (n * (size uArg)) uArg
    end
  .

  Definition type e := let tE := up e in down (size tE) tE.

  Definition size_at e p := option_map size (e @@[p]).

  Lemma down_shape1 : forall e p, IsTypedPath e p -> forall s, IsTypedPath (down s e) p.
  Proof.
    intros. generalize dependent s. induction H; intros; simpl in *;
      econstructor; firstorder.
      rewrite nth_error_map. rewrite H. reflexivity.
  Qed.

  Lemma down_shape2 : forall e p s, IsTypedPath (down s e) p -> IsTypedPath e p.
  Proof.
    induction e; intros; try (inv H; constructor; firstorder).
    inv H0. constructor. destruct (nth_error args n) eqn:Hnth;
      rewrite nth_error_map in H3; rewrite Hnth in H3; inv H3.
    econstructor. eassumption. apply (H _ _ Hnth _ _ H5).
  Qed.

  Theorem down_shape : forall e p, IsTypedPath e p <-> forall s, IsTypedPath (down s e) p.
  Proof.
    split; intros.
    - apply (down_shape1 _ _ H).
    - apply (down_shape2 _ _ 0 (H _)).
  Qed.

  Theorem up_shape : forall e p, IsPath e p <-> IsTypedPath (up e) p.
  Proof.
    split; intros.
    - induction H; simpl in *; simpl in *; try (constructor; assumption).
      econstructor.
      + rewrite nth_error_map. rewrite H. reflexivity.
      + assumption.
    - generalize dependent p. induction e; intros; simpl in *;
        try (inv H; constructor; firstorder).
      inv H0. constructor. destruct (nth_error args n) eqn:Hnth;
        rewrite nth_error_map in *; rewrite Hnth in *; inv H3. econstructor.
      + eassumption.
      + firstorder.
  Qed.

  Theorem type_shape : forall e p, IsPath e p <-> IsTypedPath (type e) p.
  Proof.
    split; intros; unfold type in *.
    - rewrite up_shape in H. apply (down_shape1 _ _ H _).
    - apply up_shape. apply (down_shape2 _ _ _ H).
  Qed.

  Lemma up_top_size : forall e, size (up e) = determine e.
  Proof.
    induction e using Expr_ind; simpl; firstorder.
    induction args.
    - reflexivity.
    - simpl. rewrite (H 0). rewrite IHargs. reflexivity. intros n.
      apply (H (S n)). reflexivity.
  Qed.

  Lemma down_top_size : forall e s, size (down s e) = s.
  Proof.
    intros; destruct e; reflexivity.
  Qed.

  Lemma type_top_size : forall e, size (type e) = determine e.
  Proof.
    intros. unfold type. rewrite up_top_size. apply down_top_size.
  Qed.

  Theorem up_size_path : forall e p, size_at (up e) p = option_map determine (e @[p]).
  Proof.
    intros; unfold size_at; destruct (IsPath_dec e p).
    - assert (HpTe: IsTypedPath (up e) p) by (apply up_shape; assumption).
      induction i; try (inv HpTe; firstorder).
      + rewrite sub_expr_nil. rewrite sub_typed_expr_nil. simpl.
        rewrite up_top_size. reflexivity.
      + simpl. rewrite H3. rewrite nth_error_map in H3. rewrite H in *. inv H3.
        firstorder.
    - assert (Hse: e @[p] = None). {
          destruct (e @[p]) eqn:Hse.
          - exfalso. apply n. apply (sub_expr_valid _ _ _ Hse).
          - reflexivity.
      }
      assert (HsTe: up e @@[p] = None). {
        destruct (up e @@[p]) eqn:HsTe.
        - exfalso. apply n. apply sub_typed_expr_valid in HsTe.
          rewrite <- up_shape in HsTe. assumption.
        - reflexivity.
      }
      rewrite Hse. rewrite HsTe. reflexivity.
  Qed.

  Ltac inv_path :=
    match goal with
    | [ H: IsPath (_ _) _ |- _ ] => inv H
    end
  .

  Lemma down_size_path_lemma :
    forall e s fc, e <== s -| fc -> forall p, IsPath e p -> fc p = size_at (down s (up e)) p.
  Proof.
    Ltac _down_size_dec :=
      match goal with
      | [ |- _ = option_map _ (down (max ?n ?m) _ @@[_]) ] =>
          let nH := fresh in destruct (max_dec_bis n m) as [[nH ?]|[nH ?]];
                             rewrite nH in *; clear nH
      end
    .
    Ltac _down_size_p_lem :=
      match goal with
      | [ H: _ = _ |- _ ] => rewrite <- H
      | [ H: _ -> _ |- _ ] => eapply H; eassumption
      | [ H: _ ==> _ -| _ |- _ ] =>
          learn (synth_must_be_determine _ _ _ H); splitHyp; subst
      | [ H: ?e ==> determine ?e -| _ |- _ ] =>
          learn (synth_can_check _ _ _ _ H (le_refl _)); existsHyp
      | [ H: ?e ==> ?t -| ?f1, F: ?e <== ?t -| ?f2 |- _ ] =>
          let nH := fresh in assert (nH: f1 = f2) by
            (extensionality p; apply (synth_check_inj_f _ _ _ _ H F));
                             learn nH; subst
      | [ H: ?e1 ==> ?t -| _, F: ?e2 <== ?t -| _ |- _ ] =>
          learn (synth_check_determine_order _ _ _ _ _ _ H F (le_refl _));
          try antisym; subst
      | [ H: ?e <== ?t -| _, F: ?t <= determine ?e |- _ ] =>
          learn (synth_and_order _ _ _ H F); subst
      end
    .
    induction e using Expr_ind; intros; simpl in *; unfold size_at; inv_path;
      try (apply check_root in H; simpl; congruence);
      inv_ts; simpl; repeat (rewrite up_top_size);
      try _down_size_dec; repeat _down_size_p_lem; try lia; try reflexivity.
    repeat (gen_nth). repeat (rewrite nth_error_map). rewrite H3. rewrite H0. simpl.
    repeat (rewrite up_top_size). specialize (H8 _ _ _ _ H3 H1 H0).
    repeat _down_size_p_lem.
  Qed.

  Theorem down_size_path : forall e s,
      determine e <= s -> e <== s -| size_at (down s (up e)).
  Proof.
    intros. destruct (always_synth e) as [t [f Hs]].
    destruct (synth_must_be_determine _ _ _ Hs). subst. clear H1.
    destruct (synth_can_check _ _ _ _ Hs H) as [fc Hc]. clear Hs. clear f.
    assert (Hfc: fc = size_at (down s (up e))).
    {
      extensionality p.
      destruct (fc p) eqn:Hfc.
      - assert (Hp: IsPath e p) by (rewrite (check_f_path _ _ _ Hc); exists n; assumption).
        rewrite <- Hfc. apply down_size_path_lemma; assumption.
      - assert (Hp: ~(IsTypedPath (down s (up e)) p)).
        { unfold not. intros. apply down_shape2 in H0. rewrite <- up_shape in H0.
          rewrite (check_f_path _ _ _ Hc) in H0. destruct H0. congruence. }
        unfold size_at. destruct (down s (up e) @@[ p]) eqn:HsTe.
        + exfalso. apply Hp. apply (sub_typed_expr_valid _ _ _ HsTe).
        + reflexivity.
    }
    rewrite <- Hfc. assumption.
  Qed.

  Theorem type_correction: forall e, exists t, e ==> t -| size_at (type e).
  Proof.
    intros. exists (determine e). destruct (always_synth e) as [t [f Hs]].
    destruct (synth_must_be_determine _ _ _ Hs); subst.
    assert (Hc: e <== determine e -| size_at (type e)).
    { unfold type. rewrite up_top_size. apply down_size_path. reflexivity. }
    assert (Hf: f = size_at (type e))
      by (extensionality p; apply (synth_check_inj_f _ _ _ _ Hs Hc)).
    subst. assumption.
  Qed.
End Algo.
