From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.

Import Expr.
Import ExprPath.
Import Path.
Import Utils.

Module Spec.
  Section SpecDef.
    Fixpoint determine e :=
      match e with
      | EAtom op => op
      | EBinOp lhs rhs => max (determine lhs) (determine rhs)
      | EUnOp arg => determine arg
      | EComp _ _ => 1
      | ELogic _ _ => 1
      | EReduction _ => 1
      | EShift lhs _ => determine lhs
      | EAssign lval _ => lval
      | ECond _ lhs rhs => max (determine lhs) (determine rhs)
      | EConcat args => sum (map determine args)
      | ERepl i arg => i * determine arg
      end
    .

    Variable e : Expr.
    Variable propagate : path -> nat.

    Definition binop_propagate := forall p lhs rhs,
        e @[p] = Some (EBinOp lhs rhs) ->
        propagate (p ++ [0]) = propagate p /\
          propagate (p ++ [1]) = propagate p.

    Definition unop_propagate := forall p arg,
        e @[p] = Some (EUnOp arg) ->
        propagate (p ++ [0]) = propagate p.

    Definition comp_propagate := forall p lhs rhs,
        e @[p] = Some (EComp lhs rhs) ->
        forall s, s = max (determine lhs) (determine rhs) ->
             propagate (p ++ [0]) = s /\
               propagate (p ++ [1]) = s.

    Definition logic_propagate := forall p lhs rhs,
        e @[p] = Some (ELogic lhs rhs) ->
        propagate (p ++ [0]) = determine lhs /\
          propagate (p ++ [1]) = determine rhs.

    Definition red_propagate := forall p arg,
        e @[p] = Some (EReduction arg) ->
        propagate (p ++ [0]) = determine arg.

    Definition shift_propagate := forall p lhs rhs,
        e @[p] = Some (EShift lhs rhs) ->
        propagate (p ++ [0]) = propagate p /\
          propagate (p ++ [1]) = determine rhs.

    Definition assign_propagate := forall p lval arg,
        e @[p] = Some (EAssign lval arg) ->
        forall s, s = max (determine arg) lval ->
             propagate (p ++ [0]) = s.

    Definition cond_propagate := forall p cond lhs rhs,
        e @[p] = Some (ECond cond lhs rhs) ->
        propagate (p ++ [0]) = determine cond /\
          propagate (p ++ [1]) = propagate p /\
          propagate (p ++ [2]) = propagate p.

    Definition concat_propagate := forall p args,
        e @[p] = Some (EConcat args) ->
        forall i f, nth_error args i = Some f ->
               propagate (p ++ [i]) = determine f.

    Definition repl_propagate := forall p i arg,
        e @[p] = Some (ERepl i arg) ->
        propagate (p ++ [0]) = determine arg.

    Definition toplevel_propagate := propagate [] = determine e.

    Definition propagate_def :=
      toplevel_propagate /\ binop_propagate /\ unop_propagate /\ comp_propagate /\
        logic_propagate /\ red_propagate /\ shift_propagate /\ assign_propagate /\
        cond_propagate /\ concat_propagate /\ repl_propagate.
  End SpecDef.

  Create HintDb Spec discriminated.

  Hint Unfold toplevel_propagate : Spec.
  Hint Unfold binop_propagate : Spec.
  Hint Unfold unop_propagate : Spec.
  Hint Unfold comp_propagate : Spec.
  Hint Unfold logic_propagate : Spec.
  Hint Unfold red_propagate : Spec.
  Hint Unfold shift_propagate : Spec.
  Hint Unfold assign_propagate : Spec.
  Hint Unfold cond_propagate : Spec.
  Hint Unfold concat_propagate : Spec.
  Hint Unfold repl_propagate : Spec.

  Hint Unfold propagate_def : Spec.


  Ltac prop_split :=
    match goal with
    | [ H: propagate_def _ _ |- _ ] =>
        destruct H as [?HTopLevel [?HBinOp [?HUnOp [?HComp [?HLogic [?HRed [?HShift [?HAssign [?HCond [?HConcat ?HRepl]]]]]]]]]]
    end
  .

  Ltac prop_gen_eq :=
    match goal with
    | [ H: toplevel_propagate _ _ |- _ ] =>
        unfold toplevel_propagate in H
    | [ F: _ @[_] = Some (EBinOp _ _), H: binop_propagate _ _ |- _ ] =>
        specialize (H _ _ _ F); destruct H
    | [ F: _ @[_] = Some (EUnOp _), H: unop_propagate _ _ |- _ ] =>
        specialize (H _ _ F)
    | [ F: _ @[_] = Some (EComp _ _), H: comp_propagate _ _ |- _ ] =>
        specialize (H _ _ _ F _ (eq_refl _)); destruct H
    | [ F: _ @[_] = Some (ELogic _ _), H: logic_propagate _ _ |- _ ] =>
        specialize (H _ _ _ F); destruct H
    | [ F: _ @[_] = Some (EReduction _), H: red_propagate _ _ |- _ ] =>
        specialize (H _ _ F)
    | [ F: _ @[_] = Some (EShift _ _), H: shift_propagate _ _ |- _ ] =>
        specialize (H _ _ _ F); destruct H
    | [ F: _ @[_] = Some (EAssign _ _), H: assign_propagate _ _ |- _ ] =>
        specialize (H _ _ _ F _ (eq_refl _))
    | [ F: _ @[_] = Some (ECond _ _ _), H: cond_propagate _ _ |- _ ] =>
        specialize (H _ _ _ _ F); destruct H as [? [? ?]]
    | [ G: nth_error _ _ = _, F: _ @[_] = Some (EConcat _),
            H: concat_propagate _ _ |- _ ] =>
        specialize (H _ _ F _ _ G)
    | [ F: _ @[_] = Some (ERepl _ _), H: repl_propagate _ _ |- _ ] =>
        specialize (H _ _ _ F)
    end
  .

   Definition cure_propagate e (f: path -> nat) p :=
    match (IsPath_dec e p) with
    | left _ => Some (f p)
    | right _ => None
    end
  .

  Theorem propagate_val : forall e f, propagate_def e f -> forall p, IsPath e p -> exists n, f p = n.
  Proof.
    induction p using path_ind; intros.
    - firstorder.
    - rewrite IsPath_chunk in H0. destruct H0 as [expr [H2 H3]].
      assert (He: IsPath e p) by apply (sub_expr_valid _ _ _ H2).
      destruct expr; inv H3; destruct (IHp He); eexists; firstorder.
  Qed.

  Theorem propagate_unique :
    forall e f1 f2, propagate_def e f1 -> propagate_def e f2 ->
               forall p, IsPath e p -> f1 p = f2 p.
  Proof.
    induction p using path_ind; intros.
    - apply eq_trans with (y := determine e). firstorder. symmetry. firstorder.
    - rewrite IsPath_chunk in H1. destruct H1 as [expr [H3 H4]].
      specialize (IHp (sub_expr_valid _ _ _ H3)).
      destruct expr; inv H4; repeat prop_split; repeat prop_gen_eq; congruence.
  Qed.

  Theorem cured_propagate_unique: forall e f1 f2,
      propagate_def e f1 -> propagate_def e f2 ->
      cure_propagate e f1 = cure_propagate e f2.
  Proof.
    intros. apply functional_extensionality. intros.
    repeat unfold cure_propagate. destruct (IsPath_dec e x).
    - rewrite (propagate_unique _ _ _ H H0 _ i). reflexivity.
    - reflexivity.
  Qed.
End Spec.

