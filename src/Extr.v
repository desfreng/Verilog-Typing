From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.

From Verilog Require Import Algo.
Import Algo.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Recursive Extraction type.
