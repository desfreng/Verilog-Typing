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

Import Notation.

Set Implicit Arguments.

Module TwoWay.

  Inductive type : nat -> Expr -> nat -> Prop :=
  | TAtom : forall n s,
      type n (EAtom s) s
  | TBinOp : forall n a b s sa sb,
      type n a sa -> type n b sb -> s = max sa sb -> type n (EBinOp a b) s
  | TUnOp : forall n e s,
      type n e s -> type n (EUnOp e) s
  | TCast : forall n e s,
      type s e s -> type n (ECast e) s
  | TComp : forall n a b s sa sb,
      type s a sa -> type s b sb -> s = max sa sb -> type n (EComp a b) 1
  | TLogic : forall n a b sa sb,
      type sa a sa -> type sb b sb -> type n (ELogic a b) 1
  | TReduction : forall n e s,
      type s e s -> type n (EReduction e) 1
  | TShift : forall n a b s sb,
      type n a s -> type sb b sb -> type n (EShift a b) s
  | TAssign : forall n lval e ne se,
      type ne e se -> ne = max se lval -> type n (EAssign lval e) lval
  | TShiftAssign : forall n lval e se,
      type se e se -> type n (EShiftAssign lval e) lval
  | TCond : forall n e a b s se sa sb,
      type se e se -> type n a se -> type n b sb -> s = max sa sb -> type n (ECond e a b) s
  | TConcat : forall n args sargs s,
      type_concat args sargs -> s = sum sargs -> type n (EConcat args) s
  | TRepl : forall n amount e se s ,
      type se e se -> s = se * amount -> type n (ERepl amount e) s

  with type_concat : list Expr -> list nat -> Prop :=
  | TConcatNil : type_concat [] []
  | TConcatCons : forall e el s sl,
      type s e s -> type_concat el sl -> type_concat (e :: el) (s :: sl)
  .

  Scheme type_rec := Induction for type Sort Prop
      with type_concat_rec := Induction for type_concat Sort Prop.

  Definition ExprHasType e n := type n e n.

  Definition e := <{ 10 + 2 + &(34) }>.

  Lemma eType: forall n, n = 10 <-> ExprHasType e n.
  Proof.
    split; intros; subst.
    - unfold e.
      apply TBinOp with (sa := 10) (sb := 1).
      + apply TBinOp with (sa := 10) (sb := 2).
        * constructor.
        * constructor.
        * reflexivity.
      + apply TReduction with (s := 34). constructor.
      + reflexivity.
    - inv H. inv H4. inv H2. inv H5. inv H3. reflexivity.
  Qed.
End TwoWay.
