# IcTheory

Lean 4 + Mathlib formalization workspace for *A theory of incremental compression*.

## Status

The development now covers the paper's foundations, the complexity layer, the Section 2/3 theorem
chain, the concrete Section 4 search-semantics layer, and the Section 5 randomness layer.

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
- Section 5 Martin-Lof randomness: paper-form Theorem 5.1 from features to randomness tests and
  paper-form Theorem 5.2 from uniform unbounded randomness tests back to a single feature

The default library target builds with `lake build`.

## Module Guide

- `IcTheory.Basics`: bitstrings, finite enumerators, prefix/pair encodings, internal encodings,
  and logarithmic bound infrastructure
- `IcTheory.Computability`: the universal machine wrapper and the complexity/information layer
- `IcTheory.Compression`: feature theory, Sections 2 to 5, the `b`-compressible scheme
  machinery, the concrete `D_s` encoding/interpreter, the paper-form Theorem 3.9 packaging, the
  paper-form Section 4 scheduler/runtime layer together with stronger current-form arithmetic
  corollaries, and the Section 5 randomness/test bridge
- `IcTheory.Sanity`: consistency checks and small integration lemmas

## Stronger Results

Besides the paper-form endpoints, the development keeps several stronger results that expose the
actual machine-level objects and constants hidden by the paper's asymptotic notation.

- `Compression.theorem39` proves exact lower and upper bounds for the concrete description object
  `D_s = ⟨s, r_s, f_s, ..., f_1⟩`, together with exact forms of the packaged eqs. (49)-(51). This
  is useful because the real bitstring, its decoder, and all overhead terms are explicit.
- `Compression.theorem41_current` retains explicit weighted-sum and closed-form search-time bounds
  stronger than the paper's asymptotic Theorem 4.1. This is useful because later proofs can reuse
  concrete arithmetic estimates instead of unpacking `O(i)` terms again.
- `Compression.theorem52_decoder` is a constructive strengthening of Theorem 5.2: it extracts a
  feature `f` and threshold `m` with `|f| = m - 1` plus an explicit decoder for the `m`-th
  randomness level set. This is useful because the randomness-to-feature map is executable and not
  merely existential.

## Build

```bash
lake build
```

## Auditing The Formalization

If you know the IC paper but not Lean, the fastest audit path is:

```bash
bash scripts/audit_claims.sh
```

That helper does four things:

1. runs `lake build`, which asks the Lean kernel to check every imported proof term in the library
2. scans `IcTheory/` for `sorry` and `admit`, which are Lean's unfinished-proof markers
3. scans `IcTheory/` for project-local `axiom`, `constant`, `opaque`, and `unsafe` declarations
   that would deserve extra scrutiny
4. runs `lake env lean IcTheory/Audit.lean`, which prints the statement actually proved
   (`#check`) and the kernel-reported axioms used by each main theorem (`#print axioms`)

How to interpret the results:

- If `lake build` succeeds, the imported theorems are fully checked by Lean's kernel.
- If the hole scan is empty, there are no unfinished proofs in `IcTheory/`.
- If the project-axiom scan is empty, the development is not introducing its own unproved logical
  assumptions through top-level declarations.
- `IcTheory/Audit.lean` shows the exact theorem types that Lean knows about, so you can compare
  them against the paper and `docs/theorem-map.md`.
- For the main theorems in this repo, `#print axioms` should report only
  `[propext, Classical.choice, Quot.sound]`, which are the standard classical axioms typically
  used by Mathlib developments. Project-local axiom names would be a red flag.
- Local commands such as `set_option maxHeartbeats ... in` only raise Lean's elaboration budget for
  expensive proofs. They do not add assumptions or weaken soundness.

## Project Notes

- `PLAN.md`
- `docs/model-decisions.md`
- `docs/theorem-map.md`
