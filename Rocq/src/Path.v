From Stdlib Require Import Lists.List.
From Stdlib Require Arith.Wf_nat.

From Verilog Require Import Utils.

Import ListNotations.
Import Wf_nat.

Import Utils.

Module Path.
  Definition path := list nat.

  Theorem path_ind : forall (P : path -> Prop), P [] -> (forall x l, P l -> P (l ++ [x])) -> forall p, P p.
  Proof.
    intros. induction p using (induction_ltof1 _ (@length _)). unfold ltof in H1.
    destruct (list_sep x) as [[a b]|] eqn:Hp.
    - apply list_sep_Some in Hp. destruct Hp as [Hp Hlen].
      rewrite Hp. apply H0. apply H1. assumption.
    - apply list_sep_None in Hp. subst. assumption.
  Qed.

  Theorem path_eq_dec : forall (a b: path), {a = b} + {a <> b}.
  Proof. decide equality. decide equality.  Qed.

End Path.
