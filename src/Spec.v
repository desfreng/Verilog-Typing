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

(** * Spec Module *)

(** This module formalizes the specification for SystemVerilog expressions bit
    sizing. *)
Module Spec.
  Section SpecDef.

    (** ** Self-Determined Size Computation — [determine] *)
    (** The function [determine] defines how each expression computes its own
        size, independent of external constraints. The computation proceeds
        recursively from operands toward the root of the AST. *)
    Fixpoint determine e :=
      match e with
      | EOperand op => op
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

    (** ** Context-Determined Size Propagation — [propagate] *)
    
    (** After [determine] computes the self-determined size of the top-level
        expression, the [propagate] process distributes *context-dependent*
        sizes back down the AST. Each subexpression receives a *final size*,
        which may differ from its self-determined size due to operator
        constraints or contextual resizing.
        
        The function [propagate : path -> nat] assigns a bitwidth to each valid
        path (subexpression) within a given expression [e]. Its behavior is
        governed by structural rules that capture how sizing information flows
        through the AST. *)
    
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
    
    (** [propagate_def] aggregates all constraints into a single specification
        stating that a function [propagate] correctly implements context-driven
        size propagation for a given expression [e]. *)
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
  
  (** ** Proof Tactics *)
  (** Helper tactics used to manipulate propagation assumptions: *)
  
  (** [prop_split]: Decomposes a hypothesis of the form [propagate_def e f]
      into its propagation rules. *)
  Ltac prop_split :=
    match goal with
    | [ H: propagate_def _ _ |- _ ] =>
        destruct H as [?HTopLevel [?HBinOp [?HUnOp [?HComp [?HLogic [?HRed [?HShift [?HAssign [?HCond [?HConcat ?HRepl]]]]]]]]]]
    end
  .

  (** [prop_gen_eq]: Specializes the appropriate propagation hypothesis
      based on the syntactic form of a subexpression found in the goal. *)
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

  (** [cure_propagate e f p]: Wraps a propagation function [f] to ensure
      it only returns a value for valid paths in [e]. Returns [Some (f p)]
      when [p] is a valid path, or [None] otherwise. *)
   Definition cure_propagate e (f: path -> nat) p :=
    match (IsPath_dec e p) with
    | left _ => Some (f p)
    | right _ => None
    end
  .

  (** ** Theorems *)
  
  (** [propagate_val]:
      For every expression [e] and valid propagation function [f],
      every valid path [p] in [e] yields the size of the expression: [f p]. *)
  Theorem propagate_val : forall e f, propagate_def e f -> forall p, IsPath e p -> exists n, f p = n.
  Proof.
    induction p using path_ind; intros.
    - firstorder.
    - rewrite IsPath_chunk in H0. destruct H0 as [expr [H2 H3]].
      assert (He: IsPath e p) by apply (sub_expr_valid _ _ _ H2).
      destruct expr; inv H3; destruct (IHp He); eexists; firstorder.
  Qed.

  (** [propagate_unique]:
      If two functions [f1] and [f2] both satisfy the specification of propagate
      for the same expression [e], then they agree on all valid paths of [e]. *)
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

  (** [cured_propagate_unique]:
      The cured (path-safe) versions of two propagate functions are
      extensionally equal. *)
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

