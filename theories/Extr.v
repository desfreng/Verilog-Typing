From Stdlib Require Import Extraction.

From Verilog Require Import Algo.
Import Algo.

Extraction Language OCaml.
Set Extraction Output Directory "extraction".

(**md Extract the typing algorithm in the output file "type.ml"  *)
Extraction "type" type.
