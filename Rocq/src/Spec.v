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
    Variable pass1 : Expr -> path -> nat.
    Variable pass2 : Expr -> path -> nat.

    Definition atom_pass1 :=
      forall e p op, e @[p] = Some (EAtom op) -> pass1 e p = op.

    Definition binop_pass1 :=
      forall e p lhs rhs,
        e @[p] = Some (EBinOp lhs rhs) ->
        pass1 e p = max (pass1 e (p ++ [Lhs])) (pass1 e (p ++ [Rhs])).

    Definition unop_pass1 :=
      forall e p arg, e @[p] = Some (EUnOp arg) -> pass1 e p = pass1 e (p ++ [Arg]).

    Definition cast_pass1 :=
      forall e p arg, e @[p] = Some (ECast arg) -> pass1 e p = pass1 e (p ++ [Arg]).

    Definition comp_pass1 :=
      forall e p lhs rhs, e @[p] = Some (EComp lhs rhs) -> pass1 e p = 1.

    Definition logic_pass1 :=
      forall e p lhs rhs, e @[p] = Some (ELogic lhs rhs) -> pass1 e p = 1.

    Definition red_pass1 :=
      forall e p arg, e @[p] = Some (EReduction arg) -> pass1 e p = 1.

    Definition shift_pass1 :=
      forall e p lhs rhs, e @[p] = Some (EShift lhs rhs) -> pass1 e p = pass1 e (p ++ [Lhs]).

    Definition assign_pass1 :=
      forall e p lval arg, e @[p] = Some (EAssign lval arg) -> pass1 e p = lval.

    Definition shiftassign_pass1 :=
      forall e p lval arg, e @[p] = Some (EShiftAssign lval arg) -> pass1 e p = lval.

    Definition cond_pass1 :=
      forall e p cond lhs rhs,
        e @[p] = Some (ECond cond lhs rhs) ->
        pass1 e p = max (pass1 e (p ++ [Lhs])) (pass1 e (p ++ [Rhs])).

    Definition concat_pass1 :=
      forall e p args pList,
        e @[p] = Some (EConcat args) ->
        (forall i, nth_error pList i = Some (pass1 e (p ++ [Args i]))) ->
        pass1 e p = sum pList.

    Definition repl_pass1 :=
      forall e p i arg, e @[p] = Some (ERepl i arg) -> pass1 e p = i * pass1 e (p ++ [Arg]).



    Definition sd e p := pass2 e p = pass1 e p.



    Definition binop_pass2 :=
      forall e p lhs rhs,
        e @[p] = Some (EBinOp lhs rhs) ->
        pass2 e (p ++ [Lhs]) = pass2 e p /\ pass2 e (p ++ [Rhs]) = pass2 e p.

    Definition unop_pass2 :=
      forall e p arg, e @[p] = Some (EUnOp arg) -> pass2 e (p ++ [Arg]) = pass2 e p.

    Definition cast_pass2 :=
      forall e p arg, e @[p] = Some (ECast arg) -> sd e (p ++ [Arg]).

    Definition comp_pass2 :=
      forall e p lhs rhs,
        e @[p] = Some (EComp lhs rhs) ->
        forall s, s = max (pass1 e (p ++ [Lhs])) (pass1 e (p ++ [Rhs])) ->
             pass2 e (p ++ [Lhs]) = s /\ pass2 e (p ++ [Rhs]) = s.

    Definition logic_pass2 :=
      forall e p lhs rhs,
        e @[p] = Some (ELogic lhs rhs) -> sd e (p ++ [Lhs]) /\ sd e (p ++ [Rhs]).

    Definition red_pass2 :=
      forall e p arg, e @[p] = Some (EReduction arg) -> sd e (p ++ [Arg]).

    Definition shift_pass2 :=
      forall e p lhs rhs, e @[p] = Some (EShift lhs rhs) ->
                     sd e (p ++ [Rhs]) /\ pass2 e (p ++ [Lhs]) = pass2 e p.

    Definition assign_pass2 :=
      forall e p lval arg,
        e @[p] = Some (EAssign lval arg) ->
        forall s, s = max (pass1 e (p ++ [Arg])) lval -> pass2 e (p ++ [Arg]) = s.

    Definition shiftassign_pass2 :=
      forall e p lval arg, e @[p] = Some (EShiftAssign lval arg) -> sd e (p ++ [Arg]).

    Definition cond_pass2 :=
      forall e p cond lhs rhs,
        e @[p] = Some (ECond cond lhs rhs) ->
        pass2 e (p ++ [Lhs]) = pass2 e p /\ pass2 e (p ++ [Rhs]) = pass2 e p /\
          sd e (p ++ [Cond]).

    Definition concat_pass2 :=
      forall e p args, e @[p] = Some (EConcat args) ->
                  forall i, i < length args -> sd e (p ++ [Args i]).

    Definition repl_pass2 :=
      forall e p i arg, e @[p] = Some (ERepl i arg) -> sd e (p ++ [Arg]).

    Definition pass1_def :=
      atom_pass1 /\ binop_pass1 /\ unop_pass1 /\ cast_pass1 /\
        comp_pass1 /\ logic_pass1 /\ red_pass1 /\ shift_pass1 /\
        assign_pass1 /\ shiftassign_pass1 /\ cond_pass1 /\ concat_pass1 /\
        repl_pass1.

    Definition pass2_def :=
      binop_pass2 /\ unop_pass2 /\ cast_pass2 /\ comp_pass2 /\
        logic_pass2 /\ red_pass2 /\ shift_pass2 /\ assign_pass2 /\
        shiftassign_pass2 /\ cond_pass2 /\ concat_pass2 /\ repl_pass2.

    Definition pass_def := pass1_def /\ pass2_def.
  End SpecDef.
End Spec.
