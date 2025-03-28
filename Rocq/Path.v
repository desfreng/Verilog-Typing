From Stdlib Require Import Lists.List.
From Stdlib Require Arith.Arith.
From Verilog Require Import Expr.

Import ListNotations.
Import Expr.

Set Implicit Arguments.

Module Path.  
  Fixpoint IsListPath {X: Type} (l: list X) idx f : Prop :=
    match l, idx with
    | x :: _, O => f x
    | _ :: tl, S i => IsListPath tl i f
    | [], _ => False
    end
  .
  
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
  
  Fixpoint IsPath (p: path) e : Prop :=
    match e, p with
    | _, [] => True
    | EBinOp lhs _, BinOpLhs :: tl => IsPath tl lhs
    | EBinOp _ rhs, BinOpRhs :: tl => IsPath tl rhs
    | EUnOp arg, UnOpArg :: tl => IsPath tl arg
    | ECast arg, CastArg :: tl => IsPath tl arg
    | EComp lhs _, CompLhs :: tl => IsPath tl lhs
    | EComp _ rhs, CompRhs :: tl => IsPath tl rhs
    | ELogic lhs _, LogicLhs :: tl => IsPath tl lhs
    | ELogic _ rhs, LogicRhs :: tl => IsPath tl rhs
    | EReduction arg, RedArg :: tl => IsPath tl arg
    | EShift lhs _, ShiftLhs :: tl => IsPath tl lhs
    | EShift _ rhs, ShiftRhs :: tl => IsPath tl rhs
    | EAssign _ arg, AssignArg :: tl => IsPath tl arg
    | EShiftAssign _ arg, ShiftAssignArg :: tl => IsPath tl arg
    | ECond cond _ _, CondCond :: tl => IsPath tl cond
    | ECond _ tb _, CondTrue :: tl => IsPath tl tb
    | ECond _ _ tf, CondFalse :: tl => IsPath tl tf
    | EUnaryConcat arg, ConcatArg :: tl => IsPath tl arg
    | EBinaryConcat lhs _, ConcatLhs :: tl => IsPath tl lhs
    | EBinaryConcat _ rhs, ConcatRhs :: tl => IsPath tl rhs
    | ERepl _ e, ReplArg :: tl => IsPath tl e
    | EInside arg _, InsideArg :: tl => IsPath tl arg
    | EInside _ l, InsideRange p :: tl => IsListPath l p (IsPath tl)
    | _, _ :: _ => False
    end
  .
    
      
  Definition add_path {X: Type} (x: X) := map (fun l => x :: l).

  Lemma add_path_okay : forall (X: Type) (l1: list X) x1 x2 l2,
    In (x1 :: l1) (add_path x2 l2) <-> x1 = x2 /\ In l1 l2.
  Proof.
    intros. apply conj; intros.
      * induction l2; destruct H.
        + inversion H. simpl. apply conj. reflexivity. left. reflexivity.
        + apply IHl2 in H. destruct H. apply conj. apply H. right. apply H0.
      * destruct H. subst. induction l2; destruct H0; simpl.
        + left. subst. reflexivity.
        + right. apply (IHl2 H).
  Qed.

  Fixpoint all_list_path {X: Type} (l: list X) :=
    match l with
    | [] => []
    | _ :: tl => O :: map S (all_list_path tl)
    end
  .

  Lemma all_list_path_length: forall (X: Type) (l: list X),
      length (all_list_path l) = length l.
  Proof.
    induction l.
    + reflexivity.
    + simpl. rewrite length_map. rewrite IHl. reflexivity.
  Qed.

  Search (?n < ?m -> S ?n < S ?m).
  
  Lemma all_list_path_values: forall (X: Type) (l: list X) x n,
      nth_error (all_list_path l) n = Some x <-> x = n /\ n < length l.
  Proof.
    induction l.
    - intros. apply conj; intros.
      + destruct n; discriminate.
      + destruct H as [H1 H2]. inversion H2.
    - intros. apply conj; intros.
      + destruct n.
        * inversion H; subst. apply conj. reflexivity. apply lt_0_succ.
        * simpl in H. rewrite nth_error_map in H. destruct (nth_error _ n) eqn:H'.
          -- inversion H. rewrite IHl in H'. intuition. apply lt_n_S_stt.
  Qed.
  

  Fixpoint zipWith {X Y Z: Type} f (l: list X) (l': list Y) : list Z :=
    match l, l' with
    | [], [] => []
    | x :: tl, y :: tl' => f x y :: zipWith f tl tl'
    | _, _ => []
    end
  .

  Lemma zipWith_length : forall (X Y Z: Type) (l: list X) (l': list Y) (f: X -> Y -> Z),
      length (zipWith f l l') = min (length l) (length l').
  Proof.
    induction l; intros.
    + destruct l'; reflexivity.
    + simpl. destruct l'.
      * reflexivity.
      * simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma zipWith_values: forall (X Y Z: Type) (l: list Y) (l': list Z) (x: X) f,
    In x (zipWith f l l') <->
      exists n y z, nth_error l n = Some y /\ nth_error l' n = Some z /\ x = f y z.
  Proof.
    induction l.
    - intros. apply conj.
      + destruct l'; contradiction.
      + intros. destruct H as [[|n] [y [z [H _]]]]; discriminate H.
    - intros. apply conj.
      + intros. destruct l'; try contradiction. destruct H.
        * exists 0. exists a. exists z. auto.
        * rewrite IHl in H. destruct H as [n [u [v H]]]. exists (S n). exists u. exists v.
          apply H.
      + intros. destruct H as [n [u [v [H1 [H2 H3]]]]]. destruct l'.
        * destruct n; discriminate H2.
        * destruct n.
          -- simpl in *. inversion H1. inversion H2. subst. auto.
          -- simpl in *. right. rewrite IHl. exists n. exists u. exists v. apply (conj H1 (conj H2 H3)).
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
        let lPath := map all_path l in
        let lPath := zipWith (fun i p => add_path (InsideRange i) p) (all_list_path l) lPath in
        [] :: add_path InsideArg (all_path arg) ++ concat lPath
    end
  .

  Lemma all_path_valid : forall e l, In l (all_path e) -> IsPath l e.
  Proof.
    Ltac UnBinTriOp :=
      match goal with
      | [ l : list ExprPath, H : In _ (all_path (_ _ _ _)) |- _ ] =>           
          destruct H;
          [ subst; constructor
          | destruct (in_app_or _ _ _ H); 
            [destruct l;
             [ constructor | rewrite add_path_okay in *; intuition (subst; eauto)]
            | edestruct in_app_or; try eassumption;
              (destruct l; [constructor
                           | rewrite add_path_okay in *; intuition (subst; eauto)])
            ]
          ]
      | [ l : list ExprPath, H : In _ (all_path (_ _ _)) |- _ ] =>           
          destruct H;
          [ subst; constructor
          | destruct (in_app_or _ _ _ H);
            (destruct l; [constructor
                         | rewrite add_path_okay in *; intuition (subst; eauto)])
          ]
      | [ l : list ExprPath, H : In _ (all_path (_ _)) |- _ ] =>
          destruct H;
          [ subst; constructor
          | destruct l;
            [constructor | rewrite add_path_okay in *; intuition (subst; eauto)]
          ]
      end.
    intros e.
    induction e using Expr_ind_bis with (P0 := fun _ => True); intros; try UnBinTriOp.
    - destruct H; [ subst; constructor | destruct H ].
    - destruct H.
      + subst. constructor.
      + destruct l.
        * constructor.
        * destruct (in_app_or _ _ _ H).
          -- rewrite add_path_okay in *. intuition (subst; eauto).
          -- rewrite in_concat in H0. destruct H0 as [x [H1 H2]].
             rewrite zipWith_values in H1. destruct H1 as [n [y [z [HA1 [HA2 HA3]]]]].
             subst. rewrite add_path_okay in *. inversion H2. subst. simpl. generalize dependent y.
  Qed.

End Verilog.
