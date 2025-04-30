From Stdlib Require Import Lists.List.
From Stdlib Require Arith.Arith.
From Stdlib Require Arith.Wf_nat.
From Verilog Require Import Expr.
From Verilog Require Import Utils.

Import ListNotations.
Import Wf_nat.

Import Expr.
Import Utils.

Set Implicit Arguments.

Module Path.
  Inductive PathItem :=
  | Lhs
  | Rhs
  | Arg
  | Cond
  | Args (i: nat)
  .

  Definition path : Type := list PathItem.

  Theorem path_ind : forall (P : path -> Prop), P [] -> (forall x l, P l -> P (l ++ [x])) -> forall p, P p.
  Proof.
    intros. induction p using (induction_ltof1 _ (@length _)). unfold ltof in H1.
    destruct (list_sep _ x Lhs).
    - subst. assumption.
    - rewrite e. apply H0. apply H1. assert (Hx: x <> []).
      + unfold not. intros. subst. discriminate e.
      + apply removelast_length. assumption.
  Qed.

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
  | P_CondTrue : forall cond tb fb p, IsPath tb p -> IsPath (ECond cond tb fb) (Lhs :: p)
  | P_CondFalse : forall cond tb fb p, IsPath fb p -> IsPath (ECond cond tb fb) (Rhs :: p)
  | P_ConcatArgs : forall n args e p,
      nth_error args n = Some e -> IsPath e p -> IsPath (EConcat args) (Args n :: p)
  | P_ReplArg : forall i arg p, IsPath arg p -> IsPath (ERepl i arg) (Arg :: p)
  .


  Lemma IsPath_prefix: forall e l1 l2, IsPath e (l1 ++ l2) -> IsPath e l1.
  Proof.
    intros e l1 l2 H. remember (l1 ++ l2).
    generalize dependent l2. generalize dependent l1. induction H; intros;
      try (destruct l1; [constructor | inversion Heql; constructor; firstorder]).
    - destruct l1.
      + constructor.
      + inv Heql. econstructor.
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
    | EAtom _ => [[]]
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
        [] :: add_path Cond (all_path cond) ++ add_path Lhs (all_path tb)
          ++ add_path Rhs (all_path fb)
    | EConcat args =>
        let lPath := mapI (fun i e => add_path (Args i) (all_path e)) args in
        [] :: concat lPath
    | ERepl _ arg => [] :: add_path Arg (all_path arg)
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
    induction e using Expr_ind;
      intros; try (split; intros; UnBinTriOp).
    - split; intros.
      + destruct H. subst. constructor. destruct H.
      + inversion H. left. reflexivity.
    - split; intros.
      + destruct H0; subst; try constructor.
        rewrite in_concat in H0. destruct H0 as [h [H1 H2]].
        rewrite mapI_values in H1. destruct H1 as [n [x [H1 H3]]].
        subst. rewrite add_path_okay in H2. destruct H2 as [p' [H2 H3]]. subst.
        econstructor. apply H1. firstorder.
      + inversion H0.
        * constructor. reflexivity.
        * subst. right. rewrite in_concat. apply (H n e H2) in H3. eexists. split.
          -- rewrite mapI_values. exists n. exists e. intuition.
          -- rewrite add_path_okay. exists p0. intuition.
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
    | ECond _ tb _, Lhs :: p => sub_expr tb p
    | ECond _ _ fb, Rhs :: p => sub_expr fb p
    | EConcat args, Args i :: p =>
        match nth_error args i with
        | Some e => sub_expr e p
        | None => None
        end
    | ERepl _ arg, Arg :: p => sub_expr arg p
    | _, _ :: _ => None
    end
  .

  Notation "e @[ p ]" := (sub_expr e p) (at level 20).

  Lemma IsPath_is_sub_expr: forall e p, IsPath e p -> exists e0, e @[p] = Some e0.
  Proof.
    intros. induction H; try (destruct IHIsPath as [x H1]; exists x);
      try (simpl; rewrite H); try (assumption). exists e. destruct e; reflexivity.
  Qed.

  Lemma sub_expr_valid: forall e p f, e @[p] = Some f -> IsPath e p.
  Proof.
    induction e using Expr_ind; intros;
      try (destruct p as [|[]]; try (discriminate H); constructor; firstorder).
      - destruct p as [|[]]; try (discriminate H); try (discriminate H0).
        + constructor.
        + simpl in H0. destruct (nth_error args i) eqn:H1; try (discriminate H0).
          econstructor. apply H1. apply (H _ _ H1 _ _ H0).
  Qed.

  Lemma IsPath_sub_expr_iff: forall e p, IsPath e p <-> exists e0, e @[p] = Some e0.
  Proof.
    split.
    - apply IsPath_is_sub_expr.
    - intros [? H]. apply (sub_expr_valid _ _ H).
  Qed.

  Lemma sub_exp_nil: forall e, e @[[]] = Some e.
  Proof.
    intros. destruct e; reflexivity.
  Qed.

  Lemma sub_exp_chunk : forall p q e g,
      (exists f, e @[p] = Some f /\ f @[q] = Some g) <-> e @[p ++ q] = Some g.
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

  Lemma IsPath_chunk : forall e p c,
      IsPath e (p ++ c) <-> (exists f, e @[p] = Some f /\ IsPath f c).
  Proof.
    split; intros.
    - destruct (IsPath_is_sub_expr H) as [g H1]. apply sub_exp_chunk in H1.
      destruct H1 as [f [H2 H3]]. exists f. split. assumption. apply IsPath_sub_expr_iff.
      exists g. assumption.
    - destruct H as [f [H1 H2]]. apply IsPath_sub_expr_iff.
      apply IsPath_sub_expr_iff in H2. destruct H2 as [g H2]. exists g.
      apply sub_exp_chunk. exists f. intuition.
  Qed.

End Path.
