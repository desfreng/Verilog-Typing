Require Import Strings.String.
Require Import Lists.List.
From coqutil Require Import Macros.ident_to_string.

Import ListNotations.

Set Implicit Arguments.

Module Verilog.
  Inductive Expr : Type :=
    | EOperand (op: string)
    | EBinOp (lhs rhs: Expr)
    | EUnOp (arg: Expr)
    | ECast (arg: Expr)
    | EComp (lhs rhs: Expr)
    | ELogicUnOp (arg: Expr)
    | ELogic (lhs rhs: Expr)
    | EReduction (arg: Expr)
    | EShift (lhs rhs: Expr)
    | EAssign (op: string) (arg: Expr)
    | EShiftAssign (op: string) (arg: Expr)
    | ECond (cond tb fb: Expr)
    | EConcat (args: list Expr)
    | ERepl (repl: nat) (args: list Expr)
    | EInside (arg: Expr) (range: list Expr)
  .

  Module ENot.
    Declare Custom Entry expr.
    Declare Custom Entry expr_var.

    Notation "a" := (ident_to_string! a) (in custom expr_var at level 0, a constr at level 0, only parsing).
    Notation "a" := (a) (in custom expr_var at level 0, a constr at level 0, format " a ", only printing).

    Notation "$( x )" := x (in custom expr at level 0, x constr, only parsing).
    Notation "<{ e }>" := e (e custom expr at level 200, only parsing).

    Notation "( x )" := x (in custom expr at level 0, x custom expr).
    Notation "x" := (EOperand x) (in custom expr at level 0, x custom expr_var at level 0).
    Notation "x + y" := (EBinOp x y) (in custom expr at level 50, left associativity).
    Notation "- x" := (EUnOp x) (in custom expr at level 0).
    Notation "'signed' ( x )" := (ECast x) (in custom expr at level 0).
    Notation "x == y" := (EComp x y) (in custom expr at level 70, left associativity).
    Notation "~ x" := (ELogicUnOp x) (in custom expr at level 0).
    Notation "x && y" := (ELogic x y) (in custom expr at level 80, left associativity).
    Notation "& x" := (EReduction x) (in custom expr at level 0).
    Notation "x >> y" := (EShift x y) (in custom expr at level 60, left associativity).
    Notation "'set' x := y" := (EAssign x y) (in custom expr at level 95, x custom expr_var, y custom expr, no associativity).
    Notation "x ? y : z" := (ECond x y z) (in custom expr at level 90, right associativity).
    Notation "{ x , .. , y }" := (EConcat (cons x .. (cons y nil) ..)) (in custom expr at level 0, x custom expr, y custom expr).
    Notation "[ i | x , .. , y ]" := (ERepl i (cons x .. (cons y nil) ..)) (in custom expr at level 0, i constr, x custom expr, y custom expr).

  End ENot.

  Import ENot.

  Inductive ExprPath :=
    | BinOpLhs
    | BinOpRhs
    | UnOpArg
    | CastArg
    | CompLhs
    | CompRhs
    | LogicArg
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
    | ConcatArg (i: nat)
    | ReplArg (i: nat)
    | InsideArg
    | InsideRange (i: nat)
  .

  Definition path : Type := list ExprPath.

  Fixpoint IsPath e (p: path) : Prop :=
    match e, p with
      | _, [] => True
      | EBinOp lhs _, BinOpLhs :: tl => IsPath lhs tl
      | EBinOp _ rhs, BinOpRhs :: tl => IsPath rhs tl
      | EUnOp arg, UnOpArg :: tl => IsPath arg tl
      | ECast arg, CastArg :: tl => IsPath arg tl
      | EComp lhs _, CompLhs :: tl => IsPath lhs tl
      | EComp _ rhs, CompRhs :: tl => IsPath rhs tl
      | ELogicUnOp arg, LogicArg :: tl => IsPath arg tl
      | ELogic lhs _, LogicLhs :: tl => IsPath lhs tl
      | ELogic _ rhs, LogicRhs :: tl => IsPath rhs tl
      | EReduction arg, RedArg :: tl => IsPath arg tl
      | EShift lhs _, ShiftLhs :: tl => IsPath lhs tl
      | EShift _ rhs, ShiftRhs :: tl => IsPath rhs tl
      | EAssign _ arg, AssignArg :: tl => IsPath arg tl
      | EShiftAssign _ arg, ShiftAssignArg :: tl => IsPath arg tl
      | ECond cond _ _, CondCond :: tl => IsPath cond tl
      | ECond _ tb _, CondTrue :: tl => IsPath tb tl
      | ECond _ _ tf, CondFalse :: tl => IsPath tf tl
      | EConcat l, ConcatArg i :: tl =>
        match nth_error l i with
          | Some e => IsPath e tl
          | None => False
        end
      | ERepl _ l, ReplArg i :: tl =>
        match nth_error l i with
          | Some e => IsPath e tl
          | None => False
        end
      | EInside arg _, InsideArg :: tl => IsPath arg tl
      | EInside _ l, InsideRange i :: tl =>
      match nth_error l i with
          | Some e => IsPath e tl
          | None => False
        end
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

  Fixpoint map_i' {X Y: Type} (f: nat -> X -> Y) (i: nat) l :=
    match l with
      | [] => []
      | hd :: tl => f i hd :: map_i' f (i + 1) tl
    end
  .

  Definition map_i {X Y: Type} (f: nat -> X -> Y) := map_i' f 0.

  Definition tag_list {X Y: Type} f g (l: list Y) : list (list X) :=
    concat (map_i (fun i e => add_path (f i) (g e)) l)
  .

  Lemma tag_list_okay : forall (X Y: Type) (l: list X) x ll g f,
    In (x :: l) (tag_list f g ll)
    <->
    exists (n: nat) (ml: list Y), nth_error ll n = Some ml /\ x = f n /\ In l (g ml).
  Proof.
      * induction ll; intros; apply conj.
        - intros. destruct H.
        - intros. destruct H as [[|y] [ml [H _]]]; discriminate H.
        - intros. remember (tag_list f g (a :: ll)). rewrite Heql0 in H.
          unfold tag_list in H. destruct (in_app_or _ _ _ H).
          + apply add_path_okay in H0. exists 0. exists a.
            apply conj. reflexivity. apply H0.
          +

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
      | ELogicUnOp arg => [] :: add_path LogicArg (all_path arg)
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
      | EConcat l => [] :: tag_list ConcatArg all_path l
      | ERepl _ l => [] :: tag_list ReplArg all_path l
      | EInside arg l => [] :: add_path InsideArg (all_path arg) ++ tag_list InsideRange all_path l
    end
  .

  Check <{test ? x + y : &{x, t, y}}>.
  Compute all_path <{test && temp ? x + y : &{-x, t, y}}>.


  Lemma in_fold_left : forall (X: Type) (l1: list X) x1 x2 l2,
    In (x1 :: l1) (fst (
      fold_left (fun acc l' => let (l, i) := acc in (_, i + 1)) l2)) -> x1 = x2 /\ In l1 l2.
  Proof.
    intros. induction l2; destruct H.
      + inversion H. simpl. apply conj. reflexivity. left. reflexivity.
      + apply IHl2 in H. destruct H. apply conj. apply H. right. apply H0.
  Qed.

  Lemma all_path_valid : forall e l, In l (all_path e) -> IsPath e l.
  Proof.
    intros e.
    induction e; intros; simpl.
    - destruct H.
      + subst. apply I.
      + destruct H.
    - destruct H.
      + subst. apply I.
      + simpl in H. apply in_app_or in H. destruct H.
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe1 _ H0).
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe2 _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. destruct l.
        * apply I.
        * rewrite in_map in H. destruct H. subst. apply (IHe _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. destruct l.
        * apply I.
        * rewrite in_map in H. destruct H. subst. apply (IHe _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. apply in_app_or in H. destruct H.
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe1 _ H0).
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe2 _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. destruct l.
        * apply I.
        * rewrite in_map in H. destruct H. subst. apply (IHe _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. apply in_app_or in H. destruct H.
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe1 _ H0).
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe2 _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. destruct l.
        * apply I.
        * rewrite in_map in H. destruct H. subst. apply (IHe _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. apply in_app_or in H. destruct H.
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe1 _ H0).
        * destruct l.
         ++ apply I.
         ++ rewrite in_map in H. destruct H. subst. apply (IHe2 _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. destruct l.
        * apply I.
        * rewrite in_map in H. destruct H. subst. apply (IHe _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. destruct l.
        * apply I.
        * rewrite in_map in H. destruct H. subst. apply (IHe _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. apply in_app_or in H. destruct H.
        * destruct l.
          ++ apply I.
          ++ rewrite in_map in H. destruct H. subst. apply (IHe1 _ H0).
        * apply in_app_or in H. destruct H.
          ++ destruct l.
            -- apply I.
            -- rewrite in_map in H. destruct H. subst. apply (IHe2 _ H0).
          ++ destruct l.
            -- apply I.
            -- rewrite in_map in H. destruct H. subst. apply (IHe3 _ H0).
    - destruct H.
      + subst. apply I.
      + simpl in H. destruct l.
        * apply I.
        * induction args.
          ++ destruct H.
          ++ simpl in H.



End Verilog.
