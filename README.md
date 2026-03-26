# IcTheory

Lean 4 + Mathlib formalization workspace for *A theory of incremental compression*.

## Status

The development has moved past the initial foundation layer.

Current compiled coverage includes:

- foundations for finite bitstrings, pairing/prefix encodings, internal encodings, and explicit
  logarithmic-slack relations
- a computability and complexity substrate built around a bitstring-facing universal machine,
  conditional complexity, prefix complexity, prefix information, finite prefix descriptions, and
  symmetry-of-information tooling
- compression definitions and Section 2 results for features, descriptive maps, singleton
  features, and the universal-feature branch
- Section 3.1 and 3.2 results, including the conditional-complexity characterizations of shortest
  features/maps, the prefix upper bounds from Lemma 3.2, and the conditional bridge
  `K(x | r) ≤ C(x | r) + O(log C(x | r))`
- Section 3.3 machinery, including a paper-facing Lemma 3.3
- a packaged Theorem 3.2 by cases
- a Theorem 3.3 reduction layer for equation (16), with the residual-side prefix bridge proved
  concretely and the remaining blocker isolated to the shortest-feature versus prefix-shortest gap

The default library target builds with `lake build`.

## Module Guide

- `IcTheory.Basics`: bitstrings, finite enumerators, prefix/pair encodings, internal encodings,
  and logarithmic bound infrastructure
- `IcTheory.Computability`: the universal machine wrapper and the complexity/information layer
- `IcTheory.Compression`: feature theory, Section 2, Section 3.1 to 3.3 developments, and the
  current Theorem 3.2 / Theorem 3.3 packaging
- `IcTheory.Sanity`: consistency checks and small integration lemmas

## Build

```bash
lake build
```

## Project Notes

- `PLAN.md`
- `docs/model-decisions.md`
- `docs/theorem-map.md`
