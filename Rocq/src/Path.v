From Stdlib Require Import Lists.List.
From Stdlib Require Arith.Arith.
From Verilog Require Import Expr.
From Verilog Require Import Utils.

Import ListNotations.
Import Expr.
Import Utils.

Set Implicit Arguments.

Module Path.
  Inductive PathItem :=
  | Lhs
  | Rhs
  | Arg
  | Cond
  | TrueB
  | FalseB
  | Args (i: nat)
  .

  Definition path : Type := list PathItem.

  Inductive IsPath : Expr -> path -> Prop :=
  | P_Empty : forall e, IsPath e []
  | P_LhsBinOp : forall lhs rhs p, IsPath lhs p -> IsPath (EBinOp lhs rhs) (Lhs :: p)
  | P_RhsBinOp : forall lhs rhs p, IsPath rhs p -> IsPath (EBinOp lhs rhs) (Rhs :: p)
  | P_UnOpArg : forall arg p, IsPath arg p -> IsPath (EUnOp arg) (Arg :: p)
  | P_CastArg : forall arg p, IsPath arg p -> IsPath (ECast arg) (Arg :: p)
  | P_LhsCompOp : forall lhs rhs p, IsPath lhs p -> IsPath (EComp lhs rhs) (Lhs :: p)
  | P_RhsCompOp : forall lhs rhs p, IsPath rhs p -> IsPath (EComp lhs rhs) (Rhs :: p)
  | P_LhsLogic : forall lhs rhs p, IsPath lhs p -> IsPath (ELogic lhs rhs) (Lhs :: p)
  | P_RhsLogic : forall lhs rhs p, IsPath rhs p -> IsPath (ELogic lhs rhs) (Rhs :: p)
  | P_RedArg : forall arg p, IsPath arg p -> IsPath (EReduction arg) (Arg :: p)
  | P_LhsShift : forall lhs rhs p, IsPath lhs p -> IsPath (EShift lhs rhs) (Lhs :: p)
  | P_RhsShift : forall lhs rhs p, IsPath rhs p -> IsPath (EShift lhs rhs) (Rhs :: p)
  | P_AssignArg : forall op arg p, IsPath arg p -> IsPath (EAssign op arg) (Arg :: p)
  | P_ShiftAssignArg : forall op arg p, IsPath arg p -> IsPath (EShiftAssign op arg) (Arg :: p)
  | P_CondCond : forall cond tb fb p, IsPath cond p -> IsPath (ECond cond tb fb) (Cond :: p)
  | P_CondTrue : forall cond tb fb p, IsPath tb p -> IsPath (ECond cond tb fb) (TrueB :: p)
  | P_CondFalse : forall cond tb fb p, IsPath fb p -> IsPath (ECond cond tb fb) (FalseB :: p)
  | P_ConcatArgs : forall n args e p,
      nth_error args n = Some e -> IsPath e p -> IsPath (EConcat args) (Args n :: p)
  | P_ReplArg : forall i arg p, IsPath arg p -> IsPath (ERepl i arg) (Arg :: p)
  | P_InsideArg : forall arg eList p, IsPath arg p -> IsPath (EInside arg eList) (Arg :: p)
  | P_InsideRange : forall n arg eList e p,
      nth_error eList n = Some e -> IsPath e p -> IsPath (EInside arg eList) (Args n :: p)
  .


  Lemma ispath_prefix: forall e p, IsPath e p -> forall l1 l2, l1 ++ l2 = p -> IsPath e l1.
  Proof.
    intros e p H. induction H; intros; try (destruct l1;
      [constructor | inversion H0; constructor; firstorder]).
    - apply app_eq_nil in H. intuition (subst; constructor).
    - destruct l1.
      + constructor.
      + inversion H1. subst. clear H1. econstructor.
        * apply H.
        * apply (IHIsPath l1 l2). reflexivity.
    - destruct l1.
      + constructor.
      + inversion H1. subst. clear H1. econstructor.
        * apply H.
        * apply (IHIsPath l1 l2). reflexivity.
  Qed.

  Definition add_path {X: Type} (x: X) := map (fun l => x :: l).

  Lemma add_path_okay : forall (X: Type) (x: X) suf l,
    In l (add_path x suf) <-> exists p, l = x :: p /\ In p suf.
  Proof.
    induction suf. intros.
    - split; intros. contradiction. destruct H as [p [_ []]].
    - split; intros.
      + destruct H.
        * subst. exists a. firstorder.
        * rewrite IHsuf in H. destruct H as [p [H1 H2]]. exists p. firstorder.
      + destruct H as [p [H1 H2]]. destruct H2; subst.
        * left. reflexivity.
        * right. apply IHsuf. exists p. firstorder.
  Qed.

  Fixpoint all_path e :=
    match e with
    | EOperand _ => [[]]
    | EBinOp lhs rhs => [] :: add_path Lhs (all_path lhs) ++ add_path Rhs (all_path rhs)
    | EUnOp arg => [] :: add_path Arg (all_path arg)
    | ECast arg => [] :: add_path Arg (all_path arg)
    | EComp lhs rhs => [] :: add_path Lhs (all_path lhs) ++ add_path Rhs (all_path rhs)
    | ELogic lhs rhs => [] :: add_path Lhs (all_path lhs) ++ add_path Rhs (all_path rhs)
    | EReduction arg => [] :: add_path Arg (all_path arg)
    | EShift lhs rhs => [] :: add_path Lhs (all_path lhs) ++ add_path Rhs (all_path rhs)
    | EAssign _ arg => [] :: add_path Arg (all_path arg)
    | EShiftAssign _ arg => [] :: add_path Arg (all_path arg)
    | ECond cond tb fb =>
        [] :: add_path Cond (all_path cond) ++ add_path TrueB (all_path tb)
          ++ add_path FalseB (all_path fb)
    | EConcat args =>
        let lPath := mapI (fun i e => add_path (Args i) (all_path e)) args in
        [] :: concat lPath
    | ERepl _ arg => [] :: add_path Arg (all_path arg)
    | EInside arg l =>
        let lPath := mapI (fun i e => add_path (Args i) (all_path e)) l in
        [] :: add_path Arg (all_path arg) ++ concat lPath
    end
  .

  Lemma all_path_valid : forall e p, In p (all_path e) <-> IsPath e p.
  Proof.
    Ltac UnBinTriOp :=
      match goal with
      | [ H : In _ (all_path (_ _ _ _)) |- _ ] =>
          destruct H;
          [ subst; constructor
          | repeat (rewrite in_app_iff in H); repeat (rewrite add_path_okay in H);
            destruct H as [[p' [H1 H2]]|[[p' [H1 H2]]|[p' [H1 H2]]]];
            subst; constructor; firstorder
          ]
      | [ H: IsPath (_ _ _ _) _ |- _ ] =>
          inversion H; subst; try (constructor; reflexivity);
          right; repeat (rewrite in_app_iff); repeat (rewrite add_path_okay);
          [left | right; left | right; right]; eexists; intuition; firstorder
      | [ H : In _ (all_path (_ _ _)) |- _ ] =>
          destruct H;
          [ subst; constructor
          | repeat (rewrite in_app_iff in H); repeat (rewrite add_path_okay in H);
            destruct H as [[p' [H1 H2]]|[p' [H1 H2]]];
            subst; constructor; firstorder
          ]
      | [ H: IsPath (_ _ _) _ |- _ ] =>
          inversion H; subst; try (constructor; reflexivity);
          right; repeat (rewrite in_app_iff); repeat (rewrite add_path_okay);
          [left | right]; eexists; intuition; firstorder
      | [ H: In _ (all_path (_ _)) |- _ ] =>
          destruct H;
          [ subst; constructor
          | repeat (rewrite in_app_iff in H); repeat (rewrite add_path_okay in H);
            destruct H as [p' [H1 H2]];
            subst; constructor; firstorder
          ]
      | [ H: IsPath (_ _) _ |- _ ] =>
          inversion H; subst; try (constructor; reflexivity);
          right; repeat (rewrite in_app_iff); repeat (rewrite add_path_okay);
          eexists; intuition; firstorder
      end.
    intro e.
    induction e using Expr_ind with
      (P0 := fun r => forall n e, nth_error r n = Some e -> forall p, In p (all_path e) <-> IsPath e p);
      intros; try (split; intros; UnBinTriOp).
    - split; intros.
      + destruct H. subst. constructor. destruct H.
      + inversion H. left. reflexivity.
    - split; intros.
      + destruct H; subst; try constructor.
        rewrite in_concat in H. destruct H as [h [H1 H2]].
        rewrite mapI_values in H1. destruct H1 as [n [x [H1 H3]]].
        subst. rewrite add_path_okay in H2. destruct H2 as [p' [H2 H3]]. subst.
        econstructor. apply H1. firstorder.
      + inversion H.
        * constructor. reflexivity.
        * subst. right. rewrite in_concat. apply (IHe n e H1) in H2. eexists. split.
          -- rewrite mapI_values. exists n. exists e. intuition.
          -- rewrite add_path_okay. exists p0. intuition.
    - split; intros.
      + destruct H; subst; try constructor. rewrite in_app_iff in *. destruct H.
        * rewrite add_path_okay in H. destruct H as [p' [H1 H2]].
          subst. constructor. firstorder.
        * rewrite in_concat in H. destruct H as [h [H1 H2]].
          rewrite mapI_values in H1. destruct H1 as [n [x [H1 H3]]].
          subst. rewrite add_path_okay in H2. destruct H2 as [p' [H2 H3]]. subst.
          econstructor. apply H1. firstorder.
      + inversion H.
        * constructor. reflexivity.
        * subst. simpl. right. rewrite in_app_iff. left. rewrite add_path_okay.
          exists p0. intuition. firstorder.
        * subst. simpl. right. rewrite in_app_iff. right. rewrite in_concat.
          apply (IHe0 n e0 H2) in H4. eexists. split.
          -- rewrite mapI_values. exists n. exists e0. intuition.
          -- rewrite add_path_okay. exists p0. intuition.
    - destruct n; discriminate H.
    - destruct n.
      + inversion H. subst. apply IHe.
      + simpl in H. firstorder.
  Qed.


  Fixpoint sub_expr (e: Expr) (p: path) :=
    match e, p with
    | e, [] => Some e
    | EBinOp lhs _, Lhs :: p => sub_expr lhs p
    | EBinOp _ rhs, Rhs :: p => sub_expr rhs p
    | EUnOp arg, Arg :: p => sub_expr arg p
    | ECast arg, Arg :: p => sub_expr arg p
    | EComp lhs _, Lhs :: p => sub_expr lhs p
    | EComp _ rhs, Rhs :: p => sub_expr rhs p
    | ELogic lhs _, Lhs :: p => sub_expr lhs p
    | ELogic _ rhs, Rhs :: p => sub_expr rhs p
    | EReduction arg, Arg :: p => sub_expr arg p
    | EShift lhs _, Lhs :: p => sub_expr lhs p
    | EShift _ rhs, Rhs :: p => sub_expr rhs p
    | EAssign _ arg, Arg :: p => sub_expr arg p
    | EShiftAssign _ arg, Arg :: p => sub_expr arg p
    | ECond cond _ _, Cond :: p => sub_expr cond p
    | ECond _ tb _, TrueB :: p => sub_expr tb p
    | ECond _ _ fb, FalseB :: p => sub_expr fb p
    | EConcat args, Args i :: p =>
        match nth_error args i with
        | Some e => sub_expr e p
        | None => None
        end
    | ERepl _ arg, Arg :: p => sub_expr arg p
    | EInside arg _, Arg :: p => sub_expr arg p
    | EInside _ args, Args i :: p =>
        match nth_error args i with
        | Some e => sub_expr e p
        | None => None
        end
    | _, _ :: _ => None
    end
  .

  Lemma IsPath_is_sub_expr: forall e p, IsPath e p -> exists e0, sub_expr e p = Some e0.
  Proof.
    intros. induction H; try (destruct IHIsPath as [x H1]; exists x);
      try (simpl; rewrite H); try (assumption). exists e. destruct e; reflexivity.
  Qed.

  Lemma sub_expr_valid: forall e p f, sub_expr e p = Some f -> IsPath e p.
  Proof.
    induction e using Expr_ind with
      (P0 := fun r => forall n e, nth_error r n = Some e ->
                          forall p f, sub_expr e p = Some f -> IsPath e p);
        intros; try (destruct p as [|[]]; try (discriminate H); constructor; firstorder).
      - destruct p as [|[]]; try (discriminate H).
        + constructor.
        + simpl in H. destruct (nth_error args i) eqn:H1; try (discriminate H).
          econstructor. apply H1. apply (IHe _ _ H1 _ _ H).
      - destruct p as [|[]]; try (discriminate H).
        + constructor.
        + constructor. firstorder.
        + simpl in H. destruct (nth_error range i) eqn:H1; try (discriminate H).
          econstructor. apply H1.  apply (IHe0 _ _ H1 _ _ H).
      - destruct n; discriminate H.
      - destruct n.
        + inversion H. subst. apply (IHe _ _ H0).
        + apply (IHe0 _ _ H _ _ H0).
  Qed.

  Lemma sub_exp_nil: forall e, sub_expr e [] = Some e.
  Proof.
    intros. destruct e; reflexivity.
  Qed.

  Lemma sub_exp_chunk : forall p q e g,
      (exists f, sub_expr e p = Some f /\ sub_expr f q = Some g)
      <-> sub_expr e (p ++ q) = Some g.
  Proof.
    induction p; split; intros.
    - destruct H as [f [H1 H2]]. rewrite sub_exp_nil in H1. inv H1. assumption.
    - exists e. split. apply sub_exp_nil. assumption.
    - destruct H as [f [H1 H2]]. destruct e; simpl; try (discriminate H1);
        destruct a; simpl in *; try (destruct (nth_error _ i));
        (apply IHp; exists f; intuition) || discriminate H1.
    - destruct a; simpl in H;
        try (destruct e; discriminate H || (apply IHp in H; assumption));
        destruct e; discriminate H || (destruct (nth_error _ i) eqn:H';
        discriminate H || (apply IHp in H; simpl; rewrite H'; assumption)).
  Qed.

  Lemma IsPath_chunk : forall e c,
      IsPath e c <-> exists p f l, sub_expr e p = Some f /\ IsPath f l /\ c = p ++ l.
  Proof.
    Ltac _is_path_chunk_tac :=
      match goal with
      | [ H: _ |- context[_ = Some ?x] ] => destruct x; reflexivity
      | [ H: _ = Some ?x |- context[_ = Some ?x] ] =>
          simpl; rewrite H; destruct x; reflexivity
      | [ C: _ = ?p ++ [], Q: sub_expr _ _ = Some ?e |- IsPath _ _] =>
          rewrite app_nil_r in C; subst; apply sub_expr_valid with (f := e); assumption
      | [ C: _ = ?p ++ ?a :: _, H: forall _, _ = _ -> _ = _ -> _,
            Q: sub_expr _ _ = Some _ |- IsPath _ _] =>
          apply (H (p ++ [a]));
          [ apply sub_exp_chunk; eexists; split; [apply Q | _is_path_chunk_tac]
          | subst; rewrite <- app_assoc; reflexivity]
      end
    .
    split; intros.
    - assert (H1: exists f, sub_expr e c = Some f). apply IsPath_is_sub_expr. assumption.
      destruct H1 as [f H1]. exists c. exists f. exists []. repeat split. assumption. constructor.
      symmetry. apply app_nil_r.
    - destruct H as [p [f [l [H1 [H2 H3]]]]].
      generalize dependent p. induction H2; intros; _is_path_chunk_tac.
  Qed.

  Lemma IsPath_suffix: forall e e0 p c l,
    IsPath e c -> c = p ++ l -> sub_expr e p = Some e0 -> IsPath e0 l.
  Proof.
  Admitted.
End Path.
