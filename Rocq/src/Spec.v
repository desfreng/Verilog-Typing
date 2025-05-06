From Stdlib Require Import Lists.List.

From Verilog Require Import Expr.
From Verilog Require Import Path.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.

Import Expr.
Import Path.
Import Utils.

Set Implicit Arguments.

Module Spec.

  Section SpecDef.
    Fixpoint determine e :=
      match e with
      | EAtom op => op
      | EBinOp lhs rhs => max (determine lhs) (determine rhs)
      | EUnOp arg => determine arg
      | ECast arg => determine arg
      | EComp _ _ => 1
      | ELogic _ _ => 1
      | EReduction _ => 1
      | EShift lhs _ => determine lhs
      | EAssign lval _ => lval
      | EShiftAssign lval _ => lval
      | ECond _ lhs rhs => max (determine lhs) (determine rhs)
      | EConcat args => sum (map determine args)
      | ERepl i arg => i * determine arg
      end
    .

    Variable propagate : Expr -> path -> nat.

    Definition binop_propagate := forall e p lhs rhs,
        e @[p] = Some (EBinOp lhs rhs) ->
        propagate e (p ++ [Left]) = propagate e p /\
          propagate e (p ++ [Right]) = propagate e p.

    Definition unop_propagate := forall e p arg,
        e @[p] = Some (EUnOp arg) ->
        propagate e (p ++ [Arg]) = propagate e p.

    Definition cast_propagate := forall e p arg,
        e @[p] = Some (ECast arg) ->
        propagate e (p ++ [Arg]) = determine arg.

    Definition comp_propagate := forall e p lhs rhs,
        e @[p] = Some (EComp lhs rhs) ->
        forall s, s = max (determine lhs) (determine rhs) ->
             propagate e (p ++ [Left]) = s /\
               propagate e (p ++ [Right]) = s.

    Definition logic_propagate := forall e p lhs rhs,
        e @[p] = Some (ELogic lhs rhs) ->
        propagate e (p ++ [Left]) = determine lhs /\
          propagate e (p ++ [Right]) = determine rhs.

    Definition red_propagate := forall e p arg,
        e @[p] = Some (EReduction arg) ->
        propagate e (p ++ [Arg]) = determine arg.

    Definition shift_propagate := forall e p lhs rhs,
        e @[p] = Some (EShift lhs rhs) ->
        propagate e (p ++ [Left]) = propagate e p /\
          propagate e (p ++ [Right]) = determine rhs.

    Definition assign_propagate := forall e p lval arg,
        e @[p] = Some (EAssign lval arg) ->
        forall s, s = max (determine arg) lval ->
             propagate e (p ++ [Arg]) = s.

    Definition shiftassign_propagate := forall e p lval arg,
        e @[p] = Some (EShiftAssign lval arg) ->
        propagate e (p ++ [Arg]) = determine arg.

    Definition cond_propagate := forall e p cond lhs rhs,
        e @[p] = Some (ECond cond lhs rhs) ->
        propagate e (p ++ [Left]) = propagate e p /\
          propagate e (p ++ [Right]) = propagate e p /\
          propagate e (p ++ [Arg]) = determine cond.

    Definition concat_propagate := forall e p args,
        e @[p] = Some (EConcat args) ->
        forall i f, nth_error args i = Some f ->
               propagate e (p ++ [Args i]) = determine f.

    Definition repl_propagate := forall e p i arg,
        e @[p] = Some (ERepl i arg) ->
        propagate e (p ++ [Arg]) = determine arg.

    Definition toplevel_propagate := forall e, propagate e [] = determine e.

    Definition propagate_def :=
      toplevel_propagate /\ binop_propagate /\ unop_propagate /\ cast_propagate /\
        comp_propagate /\ logic_propagate /\ red_propagate /\ shift_propagate /\
        assign_propagate /\ shiftassign_propagate /\ cond_propagate /\
        concat_propagate /\ repl_propagate.
  End SpecDef.

  Theorem propagate_val : forall f, propagate_def f -> forall p e, IsPath e p -> exists n, f e p = n.
  Proof.
    induction p using path_ind; intros.
    - firstorder.
    - assert (He: IsPath e p /\ exists f, e @[p] = Some f /\ IsPath f [x]).
      + split. apply (IsPath_prefix _ _ H0). apply IsPath_chunk. assumption.
      + destruct He as [H1 [expr [H2 H3]]].
        destruct expr; inv H3; destruct (IHp _ H1); try (eexists; firstorder).
  Qed.

  Ltac propagate_def_split :=
    match goal with
    | [ H: propagate_def _ |- _ ] =>
        destruct H as [?HTopLevel [?HBinOp [?HUnOp [?HCast [?HComp [?HLogic [?HRed [?HShift [?HAssign [?HShiftAssign [?HCond [?HConcat ?HRepl]]]]]]]]]]]]
    end
  .

  Theorem propagate_unique : forall p e,
      IsPath e p -> forall f1 f2, propagate_def f1 -> propagate_def f2 -> f1 e p = f2 e p.
  Proof.
    Ltac _propagate_unique_tac :=
      match goal with
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (EBinOp _ _), H: binop_propagate _ |- _ ] =>
          destruct (H _ _ _ _ F); rewrite G in *; assumption
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (EUnOp _), H: unop_propagate _ |- _ ] =>
          apply H in F; rewrite G in *; assumption
      | [ F: _ @[_] = Some (ELogic _ _), H: logic_propagate _ |- _ ] =>
          destruct (H _ _ _ _ F); assumption
      | [ F: _ @[_] = Some (EReduction _), H: red_propagate _ |- _ ] =>
          apply H in F; assumption
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (EShift _ _), H: shift_propagate _ |- _ ] =>
          destruct (H _ _ _ _ F); assumption || rewrite G in *; assumption
      | [ F: _ @[_] = Some (EAssign _ _), H: assign_propagate _ |- _ ] =>
          apply (H _ _ _ _ F); reflexivity
      | [ F: _ @[_] = Some (EShiftAssign _ _), H: shiftassign_propagate _ |- _ ] =>
          apply (H _ _ _ _ F)
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (ECond _ _ _), H: cond_propagate _ |- _ ] =>
          destruct (H _ _ _ _ _ F) as [? []]; assumption || rewrite G in *; assumption
      | [ G: nth_error _ _ = _, F: _ @[_] = Some (EConcat _),
              H: concat_propagate _ |- _ ] => apply (H _ _ _ F _ _ G)
      | [ F: _ @[_] = Some (ERepl _ _), H: repl_propagate _ |- _ ] =>
          apply (H _ _ _ _ F)
      end
    .
    assert (Heq: forall x y m : nat, x = m -> y = m -> x = y). { intros. subst. reflexivity. }
    induction p using path_ind; intros.
    - apply eq_trans with (y := determine e). firstorder. symmetry. firstorder.
    - assert (He: IsPath e p /\ exists f, e @[p] = Some f /\ IsPath f [x]).
      + split. apply (IsPath_prefix _ _ H). apply IsPath_chunk. assumption.
      + destruct He as [H2 [expr [H3 H4]]].
        assert (Hf: f1 e p = f2 e p). apply (IHp _ H2 _ _ H0 H1). clear IHp.
        destruct expr; inv H4; repeat propagate_def_split.
        * apply Heq with (m := f1 e p); _propagate_unique_tac.
        * apply Heq with (m := f1 e p); _propagate_unique_tac.
        * apply Heq with (m := f1 e p); _propagate_unique_tac.
        * apply Heq with (m := determine expr); firstorder.
        * apply Heq with (m := max (determine expr1) (determine expr2)).
          destruct (HComp0 _ _ _ _ H3 (max (determine expr1) (determine expr2))); auto.
          destruct (HComp _ _ _ _ H3 (max (determine expr1) (determine expr2))); auto.
        * apply eq_trans with (y := max (determine expr1) (determine expr2)).
          destruct (HComp0 _ _ _ _ H3 (max (determine expr1) (determine expr2))); auto.
          destruct (HComp _ _ _ _ H3 (max (determine expr1) (determine expr2))); auto.
        * apply Heq with (m := determine expr1); _propagate_unique_tac.
        * apply Heq with (m := determine expr2); _propagate_unique_tac.
        * apply Heq with (m := determine expr); _propagate_unique_tac.
        * apply Heq with (m := f1 e p); _propagate_unique_tac.
        * apply Heq with (m := determine expr2); _propagate_unique_tac.
        * apply Heq with (m := max (determine expr) lval); _propagate_unique_tac.
        * apply Heq with (m := determine expr); _propagate_unique_tac.
        * apply Heq with (m := determine expr1); _propagate_unique_tac.
        * apply Heq with (m := f1 e p); _propagate_unique_tac.
        * apply Heq with (m := f1 e p); _propagate_unique_tac.
        * apply Heq with (m := determine e0); _propagate_unique_tac.
        * apply Heq with (m := determine expr); _propagate_unique_tac.
  Qed.
End Spec.
