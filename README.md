# SystemVerilog Expression Bit-Width Determination

This repository contains research on **SystemVerilog expression bit-width determination** using **bidirectional typing**. The work provides a rigorous mathematical foundation for understanding and implementing the expression sizing semantics defined in SystemVerilog.

## Overview

SystemVerilog’s expression bit-width determination is surprisingly subtle:
an expression’s bit-width depends not only on its children but also on its parent nodes in the abstract syntax tree (AST).

This repository presents:

1. **Formal Specification** - A Rocq formalization of the IEEE 1800-2023 standard for expression bit-width determination
   ([`theory/formalization.pdf`](theory/formalization.pdf), [`src/Spec.v`](src/Spec.v)),
2. **Bidirectional Type System** - A novel typing framework capturing the context-dependent nature of SystemVerilog expressions
   ([`theory/typesystem.pdf`](theory/typesystem.pdf), [`src/TypeSystem.v`](src/TypeSystem.v)),
3. **Equivalence Proof** - Machine-checked proofs demonstrating the correspondence between our type system and the IEEE standard
   ([`src/Equiv.v`](src/Equiv.v)),
4. **Verified Algorithm** - A reference implementation with proven correctness, equivalent to our type system
   ([`src/Algo.v`](src/Algo.v)).

A Rocq extraction of the verified algorithm is available in [`src/Extr.v`](src/Extr.v).

A proposal to amend the IEEE 1800 standard is available in [`proposal/proposal.pdf`](proposal/proposal.pdf).

## Getting Started

### Verifying the Proofs

We recommend using an [opam](https://opam.ocaml.org) switch to install **Rocq version 9.0.0**:

```shell
# Create and activate a new opam switch
opam switch create verilog-typing --packages rocq-prover.9.0.0
opam switch verilog-typing

# Add the Rocq repository and install dependencies
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-navi

# Build and verify all proofs
make
```

The build process generates an interactive HTML version of the proofs in the `doc/` directory, which can be browsed locally from `doc/index.html`.

### Building the Documentation

If you have a LaTeX distribution installed, you can build the documentation in the `theory/` and `proposal/` directories with:

```shell
make tex
```
