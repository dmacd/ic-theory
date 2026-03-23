# Model Decisions

## Status

This document records the modeling choices for the Lean formalization, especially where the paper's notation does not match the most practical mathlib substrate directly.

## Decision 1: Base computability layer

We will use mathlib's partial-recursive-code infrastructure as the implementation substrate:

- `Nat.Partrec`
- `Nat.Partrec.Code`

This is the lowest-friction Lean 4 + mathlib path to a universal computation model.

## Decision 2: Paper-facing API

The paper is phrased in terms of finite binary strings and a universal machine on those strings. We will present a paper-facing API around:

- `BitString := List Bool`
- a length function for bitstrings
- pairing and self-delimiting encodings on bitstrings
- a universal evaluator for encoded programs and residuals

Internally, the evaluator may be implemented by encoding bitstrings into `Nat` and then using mathlib's universal partial-recursive machinery.

## Decision 3: Prefix complexity is a second layer, not the foundation

The paper uses prefix Kolmogorov complexity. We do not currently have an off-the-shelf prefix-complexity library in mathlib.

So the project will be structured in two layers:

1. A base description-complexity layer over the chosen universal evaluator.
2. A prefix-complexity layer built on top of it.

This avoids blocking the entire project on the hardest representation decision.

## Decision 4: The prefix bridge must be explicit

We are not treating the prefix/plain distinction as an informal implementation detail. The bridge will be formalized explicitly.

Planned bridge shape:

1. Define a self-delimiting encoding for programs and the pairing operations used in the paper.
2. Define prefix-valid programs through that encoding discipline.
3. Define prefix complexity using the same universal evaluator interface, restricted to prefix-valid codes.
4. Prove the comparison lemmas needed by the paper-level statements.

At minimum, the bridge should support:

- a precise definition of `K(x | r)` in the prefix setting
- the singleton and universal feature constructions
- the logarithmic-overhead statements used in Sections 3 and 5

## Decision 5: Theorem order

We will formalize in this order:

1. Section 2 definitions and basic lemmas.
2. Section 3.1 single-step theory.
3. Sections 3.2 to 3.5 iterative compression and `b`-compressible variants.
4. Section 4 ALICE.
5. Section 5 Martin-Lof randomness.

This keeps the main theorem chain ahead of the more specialized computable and randomness layers.
