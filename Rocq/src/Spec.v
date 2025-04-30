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
    Fixpoint pass1 e :=
      match e with
      | EAtom op => op
      | EBinOp lhs rhs => max (pass1 lhs) (pass1 rhs)
      | EUnOp arg => pass1 arg
      | ECast arg => pass1 arg
      | EComp _ _ => 1
      | ELogic _ _ => 1
      | EReduction _ => 1
      | EShift lhs _ => pass1 lhs
      | EAssign lval _ => lval
      | EShiftAssign lval _ => lval
      | ECond _ lhs rhs => max (pass1 lhs) (pass1 rhs)
      | EConcat args => sum (map pass1 args)
      | ERepl i arg => i * pass1 arg
      end
    .

    Variable pass2 : Expr -> path -> nat.

    Definition binop_pass2 :=
      forall e p lhs rhs,
        e @[p] = Some (EBinOp lhs rhs) ->
        pass2 e (p ++ [Lhs]) = pass2 e p /\ pass2 e (p ++ [Rhs]) = pass2 e p.

    Definition unop_pass2 :=
      forall e p arg, e @[p] = Some (EUnOp arg) -> pass2 e (p ++ [Arg]) = pass2 e p.

    Definition cast_pass2 :=
      forall e p arg, e @[p] = Some (ECast arg) -> pass2 e (p ++ [Arg]) = pass1 arg.

    Definition comp_pass2 :=
      forall e p lhs rhs,
        e @[p] = Some (EComp lhs rhs) ->
        forall s, s = max (pass1 lhs) (pass1 rhs) ->
             pass2 e (p ++ [Lhs]) = s /\ pass2 e (p ++ [Rhs]) = s.

    Definition logic_pass2 :=
      forall e p lhs rhs,
        e @[p] = Some (ELogic lhs rhs) -> pass2 e (p ++ [Lhs]) = pass1 lhs /\ pass2 e (p ++ [Rhs]) = pass1 rhs.

    Definition red_pass2 :=
      forall e p arg, e @[p] = Some (EReduction arg) -> pass2 e (p ++ [Arg]) = pass1 arg.

    Definition shift_pass2 :=
      forall e p lhs rhs, e @[p] = Some (EShift lhs rhs) ->
                     pass2 e (p ++ [Lhs]) = pass2 e p /\ pass2 e (p ++ [Rhs]) = pass1 rhs.

    Definition assign_pass2 :=
      forall e p lval arg,
        e @[p] = Some (EAssign lval arg) ->
        forall s, s = max (pass1 arg) lval -> pass2 e (p ++ [Arg]) = s.

    Definition shiftassign_pass2 :=
      forall e p lval arg, e @[p] = Some (EShiftAssign lval arg) -> pass2 e (p ++ [Arg]) = pass1 arg.

    Definition cond_pass2 :=
      forall e p cond lhs rhs,
        e @[p] = Some (ECond cond lhs rhs) ->
        pass2 e (p ++ [Lhs]) = pass2 e p /\ pass2 e (p ++ [Rhs]) = pass2 e p /\
          pass2 e (p ++ [Cond]) = pass1 cond.

    Definition concat_pass2 :=
      forall e p args, e @[p] = Some (EConcat args) ->
                  forall i f, nth_error args i = Some f -> pass2 e (p ++ [Args i]) = pass1 f.

    Definition repl_pass2 :=
      forall e p i arg, e @[p] = Some (ERepl i arg) -> pass2 e (p ++ [Arg]) = pass1 arg.

    Definition toplevel_pass2 := forall e, pass2 e [] = pass1 e.

    Definition pass2_def :=
      toplevel_pass2 /\ binop_pass2 /\ unop_pass2 /\ cast_pass2 /\
        comp_pass2 /\ logic_pass2 /\ red_pass2 /\ shift_pass2 /\
        assign_pass2 /\ shiftassign_pass2 /\ cond_pass2 /\
        concat_pass2 /\ repl_pass2.
  End SpecDef.

  Theorem pass2_val : forall p e, IsPath e p -> forall f, pass2_def f -> exists n, f e p = n.
  Proof.
    induction p using path_ind; intros.
    - firstorder.
    - assert (He: IsPath e p /\ exists f, e @[p] = Some f /\ IsPath f [x]).
      + split. apply (IsPath_prefix _ _ H). apply IsPath_chunk. assumption.
      + destruct He as [H1 [expr [H2 H3]]].
        destruct expr; inv H3; destruct (IHp _ H1 _ H0); try (eexists; firstorder).
  Qed.

  Ltac pass2_def_split :=
    match goal with
    | [ H: pass2_def _ |- _ ] =>
        destruct H as [?HTopLevel [?HBinOp [?HUnOp [?HCast [?HComp [?HLogic [?HRed [?HShift [?HAssign [?HShiftAssign [?HCond [?HConcat ?HRepl]]]]]]]]]]]]
    end
  .

  Theorem pass2_unique : forall p e,
      IsPath e p -> forall f1 f2, pass2_def f1 -> pass2_def f2 -> f1 e p = f2 e p.
  Proof.
    Ltac _pass2_unique_tac :=
      match goal with
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (EBinOp _ _), H: binop_pass2 _ |- _ ] =>
          destruct (H _ _ _ _ F); rewrite G in *; assumption
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (EUnOp _), H: unop_pass2 _ |- _ ] =>
          apply H in F; rewrite G in *; assumption
      | [ F: _ @[_] = Some (ELogic _ _), H: logic_pass2 _ |- _ ] =>
          destruct (H _ _ _ _ F); assumption
      | [ F: _ @[_] = Some (EReduction _), H: red_pass2 _ |- _ ] =>
          apply H in F; assumption
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (EShift _ _), H: shift_pass2 _ |- _ ] =>
          destruct (H _ _ _ _ F); assumption || rewrite G in *; assumption
      | [ F: _ @[_] = Some (EAssign _ _), H: assign_pass2 _ |- _ ] =>
          apply (H _ _ _ _ F); reflexivity
      | [ F: _ @[_] = Some (EShiftAssign _ _), H: shiftassign_pass2 _ |- _ ] =>
          apply (H _ _ _ _ F)
      | [ G: _ _ _ = _ _ _, F: _ @[_] = Some (ECond _ _ _), H: cond_pass2 _ |- _ ] =>
          destruct (H _ _ _ _ _ F) as [? []]; assumption || rewrite G in *; assumption
      | [ G: nth_error _ _ = _, F: _ @[_] = Some (EConcat _), H: concat_pass2 _ |- _ ] =>
          apply (H _ _ _ F _ _ G)
      | [ F: _ @[_] = Some (ERepl _ _), H: repl_pass2 _ |- _ ] =>
          apply (H _ _ _ _ F)
      end
    .
    assert (Heq: forall x y m : nat, x = m -> y = m -> x = y). { intros. subst. reflexivity. }
    induction p using path_ind; intros.
    - apply eq_trans with (y := pass1 e). firstorder. symmetry. firstorder.
    - assert (He: IsPath e p /\ exists f, e @[p] = Some f /\ IsPath f [x]).
      + split. apply (IsPath_prefix _ _ H). apply IsPath_chunk. assumption.
      + destruct He as [H2 [expr [H3 H4]]].
        assert (Hf: f1 e p = f2 e p). apply (IHp _ H2 _ _ H0 H1). clear IHp.
        destruct expr; inv H4; repeat pass2_def_split.
        * apply Heq with (m := f1 e p); _pass2_unique_tac.
        * apply Heq with (m := f1 e p); _pass2_unique_tac.
        * apply Heq with (m := f1 e p); _pass2_unique_tac.
        * apply Heq with (m := pass1 expr); firstorder.
        * apply Heq with (m := max (pass1 expr1) (pass1 expr2)).
          destruct (HComp0 _ _ _ _ H3 (max (pass1 expr1) (pass1 expr2))); auto.
          destruct (HComp _ _ _ _ H3 (max (pass1 expr1) (pass1 expr2))); auto.
        * apply eq_trans with (y := max (pass1 expr1) (pass1 expr2)).
          destruct (HComp0 _ _ _ _ H3 (max (pass1 expr1) (pass1 expr2))); auto.
          destruct (HComp _ _ _ _ H3 (max (pass1 expr1) (pass1 expr2))); auto.
        * apply Heq with (m := pass1 expr1); _pass2_unique_tac.
        * apply Heq with (m := pass1 expr2); _pass2_unique_tac.
        * apply Heq with (m := pass1 expr); _pass2_unique_tac.
        * apply Heq with (m := f1 e p); _pass2_unique_tac.
        * apply Heq with (m := pass1 expr2); _pass2_unique_tac.
        * apply Heq with (m := max (pass1 expr) lval); _pass2_unique_tac.
        * apply Heq with (m := pass1 expr); _pass2_unique_tac.
        * apply Heq with (m := pass1 expr1); _pass2_unique_tac.
        * apply Heq with (m := f1 e p); _pass2_unique_tac.
        * apply Heq with (m := f1 e p); _pass2_unique_tac.
        * apply Heq with (m := pass1 e0); _pass2_unique_tac.
        * apply Heq with (m := pass1 expr); _pass2_unique_tac.
  Qed.

End Spec.
