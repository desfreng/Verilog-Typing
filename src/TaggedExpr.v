From Stdlib Require Import Lists.List.

From Verilog Require Import Utils.

Import ListNotations.

Import Utils.

Module TaggedExpr.
  Section TaggedExpr_def.
    Variable T: Type.

    Unset Elimination Schemes.

    Inductive TaggedExprKind : Type :=
    | TOperand (origSize: nat)
    | TBinOp (lhs rhs: TaggedExpr)
    | TUnOp (arg: TaggedExpr)
    | TComp (lhs rhs: TaggedExpr)
    | TLogic (lhs rhs: TaggedExpr)
    | TReduction (arg: TaggedExpr)
    | TShift (lhs rhs: TaggedExpr)
    | TAssign (lval: nat) (arg: TaggedExpr)
    | TCond (cond tb fb: TaggedExpr)
    | TConcat (args: list TaggedExpr)
    | TRepl (amount: nat) (arg: TaggedExpr)
    with TaggedExpr : Type :=
    | TExpr (body: TaggedExprKind) (tag: T)
    .

    Set Elimination Schemes.

    Variable P : TaggedExpr -> Prop.

    Hypothesis HPTAtom:
      forall tag o, P (TExpr (TOperand o) tag).

    Hypothesis HPTBinOp:
      forall tag lhs rhs, P lhs -> P rhs -> P (TExpr (TBinOp lhs rhs) tag).

    Hypothesis HPTUnOp:
      forall tag arg, P arg -> P (TExpr (TUnOp arg) tag).

    Hypothesis HPTComp:
      forall tag lhs rhs, P lhs -> P rhs -> P (TExpr (TComp lhs rhs) tag).

    Hypothesis HPTLogic:
      forall tag lhs rhs, P lhs -> P rhs -> P (TExpr (TLogic lhs rhs) tag).

    Hypothesis HPTReduction:
      forall tag arg, P arg -> P (TExpr (TReduction arg) tag).

    Hypothesis HPTShift:
      forall tag lhs rhs, P lhs -> P rhs -> P (TExpr (TShift lhs rhs) tag).

    Hypothesis HPTAssign:
      forall tag op arg, P arg -> P (TExpr (TAssign op arg) tag).

    Hypothesis HPTCond:
      forall tag cond tb fb, P cond -> P tb -> P fb -> P (TExpr (TCond cond tb fb) tag).

    Hypothesis HPTConcat:
      forall tag args, (forall n e, nth_error args n = Some e -> P e) -> P (TExpr (TConcat args) tag).

    Hypothesis HPTRepl:
      forall tag n arg, P arg -> P (TExpr (TRepl n arg) tag).

    Lemma HNil: forall n e, nth_error [] n = Some e -> P e.
    Proof. intros; destruct n; inv H. Qed.

    Lemma HCons: forall hd tl,
        P hd -> (forall n e, nth_error tl n = Some e -> P e) ->
        forall n e, nth_error (hd :: tl) n = Some e -> P e.
    Proof.
      intros; destruct n; inv H1.
      - apply H.
      - apply (H0 _ _ H3).
    Qed.

    Fixpoint TaggedExpr_ind e : P e :=
      match e with
      | TExpr eKind tag =>
          match eKind with
          | TOperand o =>
              HPTAtom tag o
          | TBinOp lhs rhs =>
              HPTBinOp tag _ _ (TaggedExpr_ind lhs) (TaggedExpr_ind rhs)
          | TUnOp arg =>
              HPTUnOp tag _ (TaggedExpr_ind arg)
          | TComp lhs rhs =>
              HPTComp tag _ _ (TaggedExpr_ind lhs) (TaggedExpr_ind rhs)
          | TLogic lhs rhs =>
              HPTLogic tag _ _ (TaggedExpr_ind lhs) (TaggedExpr_ind rhs)
          | TReduction arg =>
              HPTReduction tag _ (TaggedExpr_ind arg)
          | TShift lhs rhs =>
              HPTShift tag _ _ (TaggedExpr_ind lhs) (TaggedExpr_ind rhs)
          | TAssign lval arg =>
              HPTAssign tag lval _ (TaggedExpr_ind arg)
          | TCond arg lhs rhs =>
              HPTCond tag _ _ _ (TaggedExpr_ind arg) (TaggedExpr_ind lhs) (TaggedExpr_ind rhs)
          | TConcat args =>
              HPTConcat tag args
                ((list_ind _ HNil
                    (fun hd tl => HCons _ tl (TaggedExpr_ind hd))) args)
          | TRepl n arg =>
              HPTRepl tag n _ (TaggedExpr_ind arg)
          end
      end
    .

  End TaggedExpr_def.

  Arguments TOperand {T}.
  Arguments TBinOp {T}.
  Arguments TUnOp {T}.
  Arguments TComp {T}.
  Arguments TLogic {T}.
  Arguments TReduction {T}.
  Arguments TShift {T}.
  Arguments TAssign {T}.
  Arguments TCond {T}.
  Arguments TConcat {T}.
  Arguments TRepl {T}.
  Arguments TExpr {T}.

  Definition tag {T: Type} (e: TaggedExpr T) :=
    match e with
    | TExpr _ tag => tag
    end
  .
End TaggedExpr.
