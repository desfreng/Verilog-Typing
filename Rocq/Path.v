From Stdlib Require Import Lists.List.
From Stdlib Require Arith.Arith.
From Stdlib Require Import Lia.
From Verilog Require Import Expr.

Import ListNotations.
Import Expr.
               
Set Implicit Arguments.

Module Path. 
  Inductive ExprPath :=
  | BinOpLhs
  | BinOpRhs
  | UnOpArg
  | CastArg
  | CompLhs
  | CompRhs
  | LogicLhs
  | LogicRhs
  | RedArg
  | ShiftLhs
  | ShiftRhs
  | AssignArg
  | ShiftAssignArg
  | CondCond
  | CondTrue
  | CondFalse
  | ConcatArg
  | ConcatLhs
  | ConcatRhs
  | ReplArg
  | InsideArg
  | InsideRange (i: nat)
  .

  Definition path : Type := list ExprPath.
  
  Inductive IsPath : path -> Expr -> Prop :=
  | P_Empty : forall e, IsPath [] e
  | P_LhsBinOp : forall lhs rhs p, IsPath p lhs -> IsPath (BinOpLhs :: p) (EBinOp lhs rhs)
  | P_RhsBinOp : forall lhs rhs p, IsPath p rhs -> IsPath (BinOpRhs :: p) (EBinOp lhs rhs)
  | P_UnOpArg : forall arg p, IsPath p arg -> IsPath (UnOpArg :: p) (EUnOp arg)
  | P_CastArg : forall arg p, IsPath p arg -> IsPath (CastArg :: p) (ECast arg)
  | P_LhsCompOp : forall lhs rhs p, IsPath p lhs -> IsPath (CompLhs :: p) (EComp lhs rhs)
  | P_RhsCompOp : forall lhs rhs p, IsPath p rhs -> IsPath (CompRhs :: p) (EComp lhs rhs)
  | P_LhsLogic : forall lhs rhs p, IsPath p lhs -> IsPath (LogicLhs :: p) (ELogic lhs rhs)
  | P_RhsLogic : forall lhs rhs p, IsPath p rhs -> IsPath (LogicRhs :: p) (ELogic lhs rhs)
  | P_RedArg : forall arg p, IsPath p arg -> IsPath (RedArg :: p) (EReduction arg)
  | P_LhsShift : forall lhs rhs p, IsPath p lhs -> IsPath (ShiftLhs :: p) (EShift lhs rhs)
  | P_RhsShift : forall lhs rhs p, IsPath p rhs -> IsPath (ShiftRhs :: p) (EShift lhs rhs)
  | P_AssignArg : forall op arg p, IsPath p arg -> IsPath (AssignArg :: p) (EAssign op arg)
  | P_ShiftAssignArg : forall op arg p, IsPath p arg -> IsPath (ShiftAssignArg :: p) (EShiftAssign op arg)
  | P_CondCond : forall cond tb fb p, IsPath p cond -> IsPath (CondCond :: p) (ECond cond tb fb)
  | P_CondTrue : forall cond tb fb p, IsPath p tb -> IsPath (CondTrue :: p) (ECond cond tb fb)
  | P_CondFalse : forall cond tb fb p, IsPath p fb -> IsPath (CondFalse :: p) (ECond cond tb fb)
  | P_ConcatArg : forall arg p, IsPath p arg -> IsPath (ConcatArg :: p) (EUnaryConcat arg)
  | P_ConcatLhs : forall lhs rhs p, IsPath p lhs -> IsPath (ConcatLhs :: p) (EBinaryConcat lhs rhs)
  | P_ConcatRhs : forall lhs rhs p, IsPath p rhs -> IsPath (ConcatRhs :: p) (EBinaryConcat lhs rhs)
  | P_ReplArg : forall i arg p, IsPath p arg -> IsPath (ReplArg :: p) (ERepl i arg)
  | P_InsideArg : forall arg eList p, IsPath p arg -> IsPath (InsideArg :: p) (EInside arg eList)
  | P_InsideRange : forall n arg eList e p,
      nth_error eList n = Some e -> IsPath p e -> IsPath (InsideRange n :: p) (EInside arg eList)
  .
      
  Definition add_path {X: Type} (x: X) := map (fun l => x :: l).

  Lemma add_path_okay : forall (X: Type) (x: X) suf l,
    In l (add_path x suf) <-> exists p, l = x :: p /\ In p suf.
  Proof.
    induction suf. intros.
    - split; intros. contradiction. destruct H as [p [_ []]].
    - split; intros.
      + destruct H.
        * subst. exists a. intuition.
        * rewrite IHsuf in H. destruct H as [p [H1 H2]]. exists p. intuition.
      + destruct H as [p [H1 H2]]. destruct H2; subst.
        * left. reflexivity.
        * right. apply IHsuf. exists p. intuition.
  Qed.

  Fixpoint mapI'{X Y: Type} f i (l: list X) : list Y :=
    match l with
    | [] => []
    | hd :: tl => f i hd :: mapI' f (i + 1) tl
    end
  .
  
  Definition mapI {X Y: Type} (f: nat -> X -> Y) := mapI' f 0.
                            
  Lemma mapI'_values : forall (X Y: Type) (f: nat -> X -> Y) (l: list X) y i,
      In y (mapI' f i l) <-> exists n x, nth_error l n = Some x /\ y = f (i + n) x.
  Proof.
    induction l.
    - split; intros. contradiction. destruct H as [[|n] [x [H1 H2]]]; discriminate H1.
    - split; intros.
      + destruct H as [H1 | H2].
        * exists 0. exists a. intuition. assert (HNat: i + 0 = i). lia. rewrite HNat. auto.
        * rewrite IHl in H2. destruct H2 as [n [x [H1 H2]]].
          exists (1 + n). exists x. intuition. assert (HNat: i + (1 + n) = i + 1 + n). lia.
          rewrite HNat. apply H2.
      + destruct H as [n [x [H1 H2]]]. destruct n.
        * inversion H1. subst. left. assert (HNat: i + 0 = i). lia. rewrite HNat. reflexivity.
        * right. apply IHl. exists n. exists x. intuition. assert (HNat: i + 1 + n = i + S n). lia.
          rewrite HNat. apply H2.
  Qed.

  Lemma mapI_values:  forall (X Y: Type) (f: nat -> X -> Y) (l: list X) y,
      In y (mapI f l) <-> exists n x, nth_error l n = Some x /\ y = f n x.
  Proof.
    intros. unfold mapI.  apply mapI'_values.
  Qed.
  
  Fixpoint all_path e :=
    match e with
    | EOperand _ => [[]]
    | EBinOp lhs rhs =>
        [] :: add_path BinOpLhs (all_path lhs) ++ add_path BinOpRhs (all_path rhs)
    | EUnOp arg => [] :: add_path UnOpArg (all_path arg)
    | ECast arg => [] :: add_path CastArg (all_path arg)
    | EComp lhs rhs =>
        [] :: add_path CompLhs (all_path lhs) ++ add_path CompRhs (all_path rhs)
    | ELogic lhs rhs =>
        [] :: add_path LogicLhs (all_path lhs) ++ add_path LogicRhs (all_path rhs)
    | EReduction arg => [] :: add_path RedArg (all_path arg)
    | EShift lhs rhs =>
        [] :: add_path ShiftLhs (all_path lhs) ++ add_path ShiftRhs (all_path rhs)
    | EAssign _ arg => [] :: add_path AssignArg (all_path arg)
    | EShiftAssign _ arg => [] :: add_path ShiftAssignArg (all_path arg)
    | ECond cond tb fb =>
        [] :: add_path CondCond (all_path cond) ++ add_path CondTrue (all_path tb)
          ++ add_path CondFalse (all_path fb)
    | EUnaryConcat arg => [] :: add_path ConcatArg (all_path arg)
    | EBinaryConcat lhs rhs =>
        [] :: add_path ConcatLhs (all_path lhs) ++ add_path ConcatRhs (all_path rhs)
    | ERepl _ arg => [] :: add_path ReplArg (all_path arg)
    | EInside arg l =>
        let lPath := mapI (fun i e => add_path (InsideRange i) (all_path e)) l in
        [] :: add_path InsideArg (all_path arg) ++ concat lPath
    end
  .

  Lemma all_path_valid : forall e l, In l (all_path e) <-> IsPath l e.
  Proof.
    Ltac UnBinTriOp :=
      match goal with
      | [ H : In _ (all_path (_ _ _ _)) |- _ ] =>
          destruct H;
          [ subst; constructor
          | repeat (rewrite in_app_iff in H); repeat (rewrite add_path_okay in H);
            destruct H as [[p [H1 H2]]|[[p [H1 H2]]|[p [H1 H2]]]];
            subst; constructor; firstorder
          ]
      | [ H: IsPath _ (_ _ _ _) |- _ ] =>
          inversion H; subst; try (constructor; reflexivity);
          right; repeat (rewrite in_app_iff); repeat (rewrite add_path_okay);
          [left | right; left | right; right]; eexists; intuition; firstorder
      | [ H : In _ (all_path (_ _ _)) |- _ ] =>
          destruct H;
          [ subst; constructor
          | repeat (rewrite in_app_iff in H); repeat (rewrite add_path_okay in H);
            destruct H as [[p [H1 H2]]|[p [H1 H2]]];
            subst; constructor; firstorder
          ]
      | [ H: IsPath _ (_ _ _) |- _ ] => 
          inversion H; subst; try (constructor; reflexivity);
          right; repeat (rewrite in_app_iff); repeat (rewrite add_path_okay);
          [left | right]; eexists; intuition; firstorder
      | [ H: In _ (all_path (_ _)) |- _ ] =>
          destruct H;
          [ subst; constructor
          | repeat (rewrite in_app_iff in H); repeat (rewrite add_path_okay in H);
            destruct H as [p [H1 H2]];
            subst; constructor; firstorder
          ]
      | [ H: IsPath _ (_ _) |- _ ] =>
          inversion H; subst; try (constructor; reflexivity);
          right; repeat (rewrite in_app_iff); repeat (rewrite add_path_okay);
          eexists; intuition; firstorder
      end.
    intros e.
    induction e using Expr_ind_bis with
      (P0 := fun r => forall n e, nth_error r n = Some e -> forall l, In l (all_path e) <-> IsPath l e);
      intros; try (split; intros; UnBinTriOp).
    - split; intros.
      + destruct H. subst. constructor. destruct H.
      + inversion H. left. reflexivity.
    - split; intros.
      + destruct H; subst; try constructor. rewrite in_app_iff in *. destruct H.
        * rewrite add_path_okay in H. destruct H as [p [H1 H2]].
          subst. constructor. firstorder.
        * rewrite in_concat in H. destruct H as [h [H1 H2]].
          rewrite mapI_values in H1. destruct H1 as [n [x [H1 H3]]].
          subst. rewrite add_path_okay in H2. destruct H2 as [p [H2 H3]]. subst.
          econstructor. apply H1. firstorder.
      + inversion H.
        * constructor. reflexivity.
        * subst. simpl. right. rewrite in_app_iff. left. rewrite add_path_okay.
          exists p. intuition. firstorder.
        * subst. simpl. right. rewrite in_app_iff. right. rewrite in_concat.
          apply (IHe0 n e0 H3) in H4. eexists. split.
          -- rewrite mapI_values. exists n. exists e0. intuition.
          -- rewrite add_path_okay. exists p. intuition.
    - destruct n; discriminate H.
    - destruct n.
      + inversion H. subst. apply IHe.
      + simpl in H. firstorder.
  Qed.

End Path.
