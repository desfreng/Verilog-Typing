From Stdlib Require Import Lists.List.

From Verilog Require Import Expr.
From Verilog Require Import ExprPath.
From Verilog Require Import TypedExpr.
From Verilog Require Import TypedExprPath.
From Verilog Require Import TypeSystem.
From Verilog Require Import Spec.
From Verilog Require Import Utils.

Import ListNotations.


Import Path.
Import Expr.
Import ExprPath.
Import TypedExpr.
Import TypedExprPath.
Import TypeSystem.
Import Spec.
Import Utils.

Module Algo.
  Fixpoint down s e :=
    match e with
    | TAtom _ op => TAtom s op
    | TBinOp _ tLhs tRhs => TBinOp s (down s tLhs) (down s tRhs)
    | TUnOp _ tArg => TUnOp s (down s tArg)
    | TCast _ tArg => TCast s tArg
    | TComp _ tLhs tRhs => TComp s tLhs tRhs
    | TLogic _ tLhs tRhs => TLogic s tLhs tRhs
    | TReduction _ tArg => TReduction s tArg
    | TShift _ tLhs tRhs => TShift s (down s tLhs) tRhs
    | TAssign _ lval tArg => TAssign s lval tArg
    | TShiftAssign _ lval tArg => TShiftAssign s lval tArg
    | TCond _ tArg tLhs tRhs => TCond s tArg (down s tLhs) (down s tRhs)
    | TConcat _ tArgs => TConcat s tArgs
    | TRepl _ n tArg => TRepl s n tArg
    end
  .

  Definition down_curry (x: nat * TypedExpr) := let (s, e) := x in down s e.

  Fixpoint up e :=
    match e with
    | EAtom op => (op, TAtom op op)
    | EBinOp lhs rhs =>
        let (lhsS, uLhs) := up lhs in
        let (rhsS, uRhs) := up rhs in
        let s := max lhsS rhsS in
        (s, TBinOp s uLhs uRhs)
    | EUnOp arg =>
        let (argS, uArg) := up arg in
        (argS, TUnOp argS uArg)
    | ECast arg =>
        let (argS, uArg) := up arg in
        let dArg := down argS uArg in
        (argS, TUnOp argS dArg)
    | EComp lhs rhs =>
        let (lhsS, uLhs) := up lhs in
        let (rhsS, uRhs) := up rhs in
        let s := max lhsS rhsS in
        let dLhs := down s uLhs in
        let dRhs := down s uRhs in
        (1, TComp 1 dLhs dRhs)
    | ELogic lhs rhs =>
        let (lhsS, uLhs) := up lhs in
        let (rhsS, uRhs) := up rhs in
        let dLhs := down lhsS uLhs in
        let dRhs := down rhsS uRhs in
        (1, TLogic 1 dLhs dRhs)
    | EReduction arg =>
        let (argS, uArg) := up arg in
        let dArg := down argS uArg in
        (1, TReduction 1 dArg)
    | EShift lhs rhs =>
        let (lhsS, uLhs) := up lhs in
        let (rhsS, uRhs) := up rhs in
        let dRhs := down rhsS uRhs in
        (lhsS, TLogic lhsS uLhs dRhs)
    | EAssign lval arg =>
        let (argS, uArg) := up arg in
        let s := max lval argS in
        let dArg := down s uArg in
        (lval, TAssign lval lval dArg)
    | EShiftAssign lval arg =>
        let (argS, uArg) := up arg in
        let dArg := down argS uArg in
        (lval, TAssign lval lval dArg)
    | ECond arg lhs rhs =>
        let (argS, uArg) := up arg in
        let (lhsS, uLhs) := up lhs in
        let (rhsS, uRhs) := up rhs in
        let s := max lhsS rhsS in
        let dArg := down argS uArg in
        (s, TCond s dArg uLhs uRhs)
    | EConcat args =>
        let uArgs := map up args in
        let dArgs := map down_curry uArgs in
        let s := sum (map fst uArgs) in
        (s, TConcat s dArgs)
    | ERepl n arg =>
        let (argS, uArg) := up arg in
        let dArg := down argS uArg in
        let s := n * argS in
        (s, TReduction s dArg)
    end
  .

  Definition type e := down_curry (up e).

  Definition size_at e p := option_map size (e @@[p]).

  Theorem down_shape : forall e p s, IsTypedPath e p <-> IsTypedPath (down s e) p.
  Proof.
    split; intros.
    - induction H; simpl in *; econstructor; eassumption.
    - generalize dependent p. induction e; intros; simpl in *;
        try (inv H; constructor; firstorder).
      inv H0. constructor. econstructor; eassumption.
  Qed.

  Theorem up_shape : forall e p, IsPath e p <-> IsTypedPath (snd (up e)) p.
  Proof.
    split; intros.
    Ltac _up_shape :=
      match goal with
      | [ |- IsTypedPath (snd (let (_, _) := up ?e in _)) _ ] => destruct (up e)
      | [ H: IsTypedPath (snd (let (_, _) := up ?e in _)) _ |- _ ] => destruct (up e)
      | [ H: IsTypedPath (down _ _) _ |- _ ] => rewrite <- down_shape in H
      end
    .
    - induction H; simpl in *; repeat _up_shape; simpl in *; try constructor;
        try (apply down_shape); try assumption.
      econstructor.
      + repeat (rewrite nth_error_map). rewrite H. simpl in *. reflexivity.
      + destruct (up e). simpl in *. apply down_shape. assumption.
    - generalize dependent p. induction e; intros; simpl in *; repeat _up_shape;
        simpl in *; try (inv H); try constructor; repeat _up_shape; try firstorder.
      inv H0.
      + constructor.
      + repeat (rewrite nth_error_map in H3). destruct (nth_error args n) eqn:HArg;
        inv H3. econstructor.
        * eassumption.
        * eapply H. eassumption. destruct (up e0). simpl in *.
          rewrite <- down_shape in H5. assumption.
  Qed.

  Theorem type_shape : forall e p, IsPath e p <-> IsTypedPath (type e) p.
  Proof.
    intros. unfold type. destruct (up e) eqn:Hup. simpl. rewrite <- down_shape.
    assert (Ht: t = snd (up e)) by (rewrite Hup; reflexivity). subst. apply up_shape.
  Qed.

  Hint Unfold type : core.
  Hint Unfold size_at : core.
  Hint Unfold down_curry : core.

  Theorem up_size : forall e, fst (up e) = determine e.
  Proof.
    Ltac _up_size :=
      match goal with
      | [ |- fst (let (_, _) := up ?e in _) = _ ] => destruct (up e)
      | [ H: fst (up ?e) = _ |- _ ] => destruct (up e)
      end
    .
    induction e using Expr_ind; autounfold; simpl;
      repeat _up_size; simpl in *; try congruence.
    induction args.
    - reflexivity.
    - simpl. rewrite (H 0 _ (eq_refl _)). rewrite IHargs.
      + reflexivity.
      + intros n. apply (H (S n)).
  Qed.

  Theorem down_size : forall e s, size (down s e) = s.
  Proof.
    intros [] ?; reflexivity.
  Qed.

  Theorem type_size : forall e, size (type e) = determine e.
  Proof.
    intros. autounfold. destruct (up e) eqn:Hup.
    assert (fst (up e) = n) by (rewrite Hup; reflexivity).
    rewrite down_size. rewrite <- H. apply up_size.
  Qed.

  Theorem ttoreike : forall e t f,
      e ==> t -| f -> forall p, IsPath e p -> size_at (type e) p = f p.
  Proof.
    intros. induction p using path_ind.
    - unfold size_at. rewrite sub_typed_expr_nil. simpl. rewrite type_size.
      destruct (synth_must_be_determine H). congruence.
    - unfold size_at. admit.
  Admitted.

End Algo.


