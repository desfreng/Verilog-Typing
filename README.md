# SystemVerilog Expression Bit-Width Determination

This repository contains a Rocq formalization of SystemVerilog expression bit-width determination, including a bidirectional type system, equivalence proofs against the specification, and a verified algorithm.

## How to build

### Prerequisites

- [opam](https://opam.ocaml.org)
- Rocq 9.0.0 (recommended via an opam switch)
- `rocq-navi` (for `make doc`)
- `latexmk` (optional, only for `make tex`)

### Reproducible setup and proof checking

Run the following commands from the repository root:

```sh
# Create and activate a dedicated Rocq switch
opam switch create verilog-typing --packages rocq-prover.9.0.0
eval "$(opam env --switch=verilog-typing --set-switch)"

# Add the Rocq package repository and install doc dependency
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-navi

# Required for artifact evaluation (proof checking)
make build

# Also valid: build + HTML documentation
make

# Explicit documentation target
make doc

# Optional: build LaTeX PDFs under formalisation/ and proposal/
make tex

# Optional cleanup
make clean
```

### Expected outputs

- `make build` verifies the development in `theories/`.
- `make doc` generates browsable documentation at `doc/index.html`.
- Building `theories/Extr.v` produces extracted code under `extraction/`.

## Directory organisation

| Path             | Kind      | Purpose for evaluation                                                               |
| ---------------- | --------- | ------------------------------------------------------------------------------------ |
| `theories/`      | Source    | Rocq formalization (specification, type system, equivalence, algorithm, extraction). |
| `formalisation/` | Source    | LaTeX formal equations and write-up material.                                        |
| `proposal/`      | Source    | Amendment proposal text and PDF build inputs.                                        |
| `doc/`           | Generated | HTML proof/documentation output from `make doc` or `make`.                           |
| `extraction/`    | Generated | Extracted OCaml code (e.g., `type.ml`) from extraction modules.                      |

## Paper-to-Rocq traceability

| Paper entry                                 | Rocq symbol(s)                                                                                                                                                                                                                  | Rocq file               |
| ------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------- |
| Figure 2: expression grammar                | `Expr` constructors (`EOperand`, `EBinOp`, `EUnOp`, `EComp`, `ELogic`, `EReduction`, `EShift`, `EAssign`, `ECond`, `EConcat`, `ERepl`)                                                                                          | `theories/Expr.v`       |
| Figure 3: Determine function                | `determine`                                                                                                                                                                                                                     | `theories/Spec.v`       |
| Figure 4: LRM-derived propagate constraints | `propagate_def`, `toplevel_propagate`, `binop_propagate`, `unop_propagate`, `comp_propagate`, `logic_propagate`, `red_propagate`, `shift_propagate`, `assign_propagate`, `cond_propagate`, `concat_propagate`, `repl_propagate` | `theories/Spec.v`       |
| Figure 5: sizing function combinators       | `Initial`, `ReplaceRoot`, `Binary`, `Unary`, `Ternary`, `Nary`                                                                                                                                                                  | `theories/TypeSystem.v` |
| Figure 6: resizing rules                    | `ResizeC`, `BinOpC`, `UnOpC`, `ShiftC`, `CondC`                                                                                                                                                                                 | `theories/TypeSystem.v` |
| Figure 7: self-determined width rules       | `AtomS`, `LBinOpS`, `RBinOpS`, `UnOpS`, `LCompS`, `RCompS`, `LogicS`, `RedS`, `ShiftS`, `LAssignS`, `RAssignS`, `LCondS`, `RCondS`, `ConcatS`, `ReplS`                                                                          | `theories/TypeSystem.v` |
| Lemma 1: Universal Derivations              | `always_synth`, `always_check`                                                                                                                                                                                                  | `theories/TypeSystem.v` |
| Lemma 2: Derivation Determinism             | `synth_inj`, `synth_inj_f`, `check_inj_f`                                                                                                                                                                                       | `theories/TypeSystem.v` |
| Lemma 3: Synthesis-Checking Equivalence     | `synth_check`                                                                                                                                                                                                                   | `theories/TypeSystem.v` |
| Theorem 1: Synthesis as Minimal Width       | `synth_minimal_check`                                                                                                                                                                                                           | `theories/TypeSystem.v` |
| Lemma 4: Sub-expression Synthesis           | `synth_sub_expr`                                                                                                                                                                                                                | `theories/TypeSystem.v` |
| Lemma 5: Sub-expression Checking            | `check_sub_expr`                                                                                                                                                                                                                | `theories/TypeSystem.v` |
| Lemma 6: Synthesis Computes Determine       | `synth_determine`                                                                                                                                                                                                               | `theories/Equiv.v`      |
| Lemma 7: Specification Implies Rule System  | `spec_implies_ts`                                                                                                                                                                                                               | `theories/Equiv.v`      |
| Lemma 8: Rule System Implies Specification  | `ts_implies_spec`                                                                                                                                                                                                               | `theories/Equiv.v`      |
| Theorem 2: Rule System-LRM Equivalence      | `ts_equiv_spec`                                                                                                                                                                                                                 | `theories/Equiv.v`      |
| Theorem 3: Algorithm Correctness            | `type_correction`                                                                                                                                                                                                               | `theories/Algo.v`       |
