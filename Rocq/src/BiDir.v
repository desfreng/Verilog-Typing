From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import PeanoNat.
From Verilog Require Import Expr.
From Verilog Require Import Path.
From Verilog Require Import Utils.

Import ListNotations.
Import Nat.
Import Expr.
Import Path.
Import Utils.

Set Implicit Arguments.

Module BiDir.

  Inductive Resizable : Expr -> Prop :=
  | ResAtom : forall op, Resizable (EAtom op)
  | ResCast : forall e, Resizable (ECast e)
  | ResComp : forall lhs rhs, Resizable (EComp lhs rhs)
  | ResLogic : forall lhs rhs, Resizable (ELogic lhs rhs)
  | ResRed : forall e, Resizable (EReduction e)
  | ResAssign : forall lval arg, Resizable (EAssign lval arg)
  | ResShiftAssign : forall lval arg, Resizable (EShiftAssign lval arg)
  | ResConcat : forall args, Resizable (EConcat args)
  | ResRepl : forall amount arg, Resizable (ERepl amount arg)
  | ResInside : forall arg args, Resizable (EInside arg args)
  .

  Fixpoint sum (l: list nat) :=
    match l with
    | [] => 0
    | hd :: tl => hd + sum tl
    end
  .

  Reserved Notation "e '==>' t" (at level 90).
  Reserved Notation "e '==>l' t" (at level 90).
  Reserved Notation "e '<==' t" (at level 90).
  Reserved Notation "e '<==l' t" (at level 90).

  Inductive synth : Expr -> nat -> Prop :=
  | AtomS op : EAtom op ==> op

  | LBinOpS a b t :
      a ==> t ->
      b <== t ->
      (* ========== *)
      EBinOp a b ==> t

  | RBinOpS a b t :
      a <== t ->
      b ==> t ->
      (* ========== *)
      EBinOp a b ==> t

  | UnOpS e t :
    e ==> t ->
    (* ========== *)
    EUnOp e ==> t

  | CastS e t :
    e ==> t ->
    (* ========== *)
    ECast e ==> t

  | LCompS a b t :
    a ==> t ->
    b <== t ->
    (* ========== *)
    EComp a b ==> 1

  | RCompS a b t :
    a <== t ->
    b ==> t ->
    (* ========== *)
    EComp a b ==> 1

  | LogicS a b ta tb :
    a ==> ta ->
    b ==> tb ->
    (* ========== *)
    ELogic a b ==> 1

  | RedS e t :
    e ==> t ->
    (* ========== *)
    EReduction e ==> 1

  | Shift a b t tb :
    a ==> t ->
    b ==> tb ->
    (* ========== *)
    EShift a b ==> t

  | LAssignS lval e :
    e <== lval ->
    (* ========== *)
    EAssign lval e ==> lval

  | RAssignS lval e te :
    e ==> te ->
    lval < te ->
    (* ========== *)
    EAssign lval e ==> lval

  | AssignShiftS lval e te :
    e ==> te ->
    (* ========== *)
    EShiftAssign lval e ==> lval

  | LCondS e a b t te :
    e ==> te ->
    a ==> t ->
    b <== t ->
    (* ========== *)
    ECond e a b ==> t

  | RCondS e a b t te :
    e ==> te ->
    a <== t ->
    b ==> t ->
    (* ========== *)
    ECond e a b ==> t

  | ConcatS args ts t :
    args ==>l ts ->
    t = sum ts ->
    (* ========== *)
    EConcat args ==> t

  | ReplS i e te t :
    e ==> te ->
    t = i * te ->
    (* ========== *)
    ERepl i e ==> t

  | LInsideS a args t :
    a ==> t ->
    args <==l t ->
    (* ========== *)
    EInside a args ==> t

  | RInsideS a args e t :
    In e args ->
    e ==> t ->
    a <== t ->
    args <==l t ->
    (* ========== *)
    EInside a args ==> t

  where "e '==>' n" := (synth e n)

  with synthList : list Expr -> list nat -> Prop :=
  | SynthNil : [] ==>l []

  | SynthCons e t eL tL :
    e ==> t ->
    eL ==>l tL ->
    (* ========== *)
    (e :: eL) ==>l (t :: tL)

  where "e '==>l' n" := (synthList e n)

  with check : Expr -> nat -> Prop :=
  | ResizeC e s t :
      Resizable e ->
      e ==> s ->
      s <= t ->
      (* ========== *)
      e <== t

  | BinOpC a b t :
      a <== t ->
      b <== t ->
      (* ========== *)
      EBinOp a b <== t

  | UnOpC e t :
      e <== t ->
      (* ========== *)
      EUnOp e <== t

  | ShiftC a b t tb :
      a <== t ->
      b ==> tb ->
      (* ========== *)
      EShift a b <== t

  | CondC e a b t te :
      e ==> te ->
      a <== t ->
      b <== t ->
      (* ========== *)
      ECond e a b <== t

  where "e '<==' n" := (check e n)

  with checkList : list Expr -> nat -> Prop :=
  | CheckNil t : [] <==l t

  | CheckCons e eL t :
    e <== t ->
    eL <==l t ->
    (* ========== *)
    (e :: eL) <==l t

  where "e '<==l' n" := (checkList e n)
  .


  Lemma check_can_grow : forall e t s, e <== t -> t <= s -> e <== s.
  Proof.
    Ltac _check_can_grow_tac :=
      match goal with
      | [ HRes: Resizable _, H: ?e ==> ?x, Hle: ?x <= ?y |- ?e <== ?z ] =>
          apply (ResizeC HRes H); apply (le_trans x y z); assumption
      | [ H: _ <== _ |- _ <== _ ] => inv H; _check_can_grow_tac
      end
    .
    induction e using Expr_ind; intros; try _check_can_grow_tac.
    - inv H. inv H1. constructor. firstorder. firstorder.
    - inv H. inv H1. constructor. firstorder.
    - inv H. inv H1. assert (H : e1 <== s). firstorder. apply (ShiftC H H5).
    - inv H. inv H1. apply (CondC H4). firstorder. firstorder.
  Qed.

  Theorem synth_can_check : forall e t, e ==> t -> forall s, t <= s -> e <== s.
  Proof.
    induction e using Expr_ind; intros;
      try (apply ResizeC with (s := t0); [constructor | assumption | assumption]).
    - inv H.
      + constructor. firstorder. apply (check_can_grow H5 H0).
      + constructor. apply (check_can_grow H3 H0). firstorder.
    - inv H. constructor. firstorder.
    - inv H. assert (H: e1 <== s). firstorder. apply (ShiftC H H5).
    - inv H.
      + apply (CondC H4). firstorder. apply (check_can_grow H7 H0).
      + apply (CondC H4). apply (check_can_grow H6 H0). firstorder.
  Qed.

  Lemma synth_implies_check: forall e t, e ==> t -> e <== t.
  Proof.
    intros. apply synth_can_check with (t := t0). assumption. constructor.
  Qed.
End BiDir.
