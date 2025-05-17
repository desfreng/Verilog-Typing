From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.

From Verilog Require Import Algo.
Import Algo.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "succ" ].

Extract Constant Nat.add => "( + )".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.max => "(fun x y -> max x y)".

