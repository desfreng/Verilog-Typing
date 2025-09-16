# SystemVerilog Expression Bit-Width Determination

This repository contains the research work on SystemVerilog expression bit-width
determination using bidirectional typing. This work provides a mathematical
foundation for understanding and implementing SystemVerilog's expression sizing
semantics.

## Overview

SystemVerilog's expression bit-width determination is surprisingly subtle, as an
expression's bit-width depends on both its children and its parents in the
abstract syntax tree.

This repository presents:

1. **Formal Specification**: A Rocq formalization of the IEEE 1800-2023 standard
for expression bit-width determination,
2. **Bidirectional Type System**: A novel typing framework that captures the
context-dependent nature of SystemVerilog expressions,
3. **Equivalence Proof**: Machine-checked proofs establishing the correspondence
between our type system and the IEEE standard,
4. **Verified Algorithm**: A reference implementation with correctness
guarantees, proven equivalent to our type system.

## Repository Contents

### Theory and Formalization

- **IEEE 1800 Formalization** (`theory/formalization.pdf`): Mathematical
interpretation of the SystemVerilog standard's prose descriptions for bit-width
determination.
- **Bidirectional Type System** (`theory/typesystem.pdf`): Formal typing rules
that capture self-determined and context-determined expression sizing.

### Mechanized Proofs

- **Rocq Formalization** (`src/`): Complete machine-checked proofs of
equivalence between our type system and the IEEE specification.
- **Interactive Proofs**: Browse the proofs online at
[https://gabriel.desfrene.fr/verilog/proof](https://gabriel.desfrene.fr/verilog/proof).
- **Verified Algorithm** (`src/Algo.v`): Reference implementation with
correctness proofs.
- **OCaml Extraction** (`src/Extr.v`): Rocq extraction of the verified Algorithm.

### Standardization Contributions

- **IEEE 1800 Improvement Proposal**: Available at
[https://gabriel.desfrene.fr/verilog/proposal.pdf](https://gabriel.desfrene.fr/verilog/proposal.pdf)
- Addresses ambiguities in the current standard while maintaining backward compatibility

## Getting Started

### Prerequisites

- **LaTeX Distribution**: TeX Live or similar for building documentation
- **Rocq Prover**: Version 9.0.0 or compatible

### Building the Documentation

```shell
latexmk -pdf theory/formalization.tex
latexmk -pdf theory/typesystem.tex
```

### Verifying the Proofs

We recommend using an opam switch for dependency management:

```shell
# Create and activate a new opam switch
opam switch create verilog-typing --packages rocq-prover.9.0.0
opam switch verilog-typing

# Add Rocq repository and install dependencies
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-navi

# Build and verify all proofs
dune build
```

The build process generates an interactive HTML version of the proofs in
`_build/default/src/html/` that can be browsed locally.

## Authors

- Gabriel Desfrene (École normale supérieure -- PSL)
- Quentin Corradi (Imperial College London) 
- Michalis Pardalos (Imperial College London)
- John Wickerson (Imperial College London)
