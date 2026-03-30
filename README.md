# IcTheory

Lean 4 + Mathlib formalization workspace for *A theory of incremental compression*.

## Status

The development now covers the paper's foundations, the complexity layer, the Section 2/3 theorem
chain, and a concrete Section 4 search-semantics layer.

Current compiled coverage includes:

- foundations for finite bitstrings, pairing/prefix encodings, internal encodings, and explicit
  logarithmic-slack relations
- a computability and complexity substrate built around a bitstring-facing universal machine,
  conditional complexity, prefix complexity, prefix information, finite prefix descriptions, and
  symmetry-of-information tooling
- compression definitions and Section 2 results for features, descriptive maps, singleton
  features, and the universal-feature branch
- Sections 3.1 to 3.5, including packaged paper-form Theorems 3.1 to 3.9 and the
  `b`-feature transfer layer
- the concrete Section 3.5 description object `D_s = ⟨s, r_s, f_s, ..., f_1⟩`, together with
  decoding, interpreters, and explicit length/prefix-complexity bounds
- Section 4 autoencoder/search semantics: encoded autoencoder payloads and outputs, the fixed
  interpreter `W`, ALICE / Greedy-ALICE branch semantics, concrete phase programs and budgets,
  paper-form Lemma 4.1 for the live scheduler, and paper-form Theorem 4.1 showing that
  incremental `b`-compression schemes induce ALICE branches whose descriptions reconstruct `x`
  and whose search cost is bounded by the paper-style weighted sum

The default library target builds with `lake build`.

## Module Guide

- `IcTheory.Basics`: bitstrings, finite enumerators, prefix/pair encodings, internal encodings,
  and logarithmic bound infrastructure
- `IcTheory.Computability`: the universal machine wrapper and the complexity/information layer
- `IcTheory.Compression`: feature theory, Sections 2 to 4, the `b`-compressible scheme
  machinery, the concrete `D_s` encoding/interpreter, the paper-form Theorem 3.9 packaging, and
  the paper-form Section 4 scheduler/runtime layer together with stronger current-form arithmetic
  corollaries
- `IcTheory.Sanity`: consistency checks and small integration lemmas

## Build

```bash
lake build
```

## Project Notes

- `PLAN.md`
- `docs/model-decisions.md`
- `docs/theorem-map.md`
