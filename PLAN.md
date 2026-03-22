# Lean Formalization Plan for "A Theory of Incremental Compression"

## Goal

Formalize the core theory in [1908.03781v2.pdf](./1908.03781v2.pdf) in Lean 4, with enough structure to later add the computable algorithmic pieces and the Martin-Lof randomness bridge.

The paper naturally breaks into four layers:

1. Strings, encodings, and a universal computation model.
2. Kolmogorov-style description complexity and feature/residual definitions.
3. The incremental-compression theorem chain in Sections 2 and 3.
4. The later computable and randomness layers in Sections 4 and 5.

## Recommended Technical Stance

### 1. Use Lean 4 + mathlib, not bare Lean

The project should be a normal `lake` package with a mathlib dependency. mathlib already contains the main raw ingredients you need:

- encodings and countability infrastructure
- partial recursive functions and executable codes
- Turing-machine formalisms
- some coding-theory results such as Kraft-McMillan

### 2. Start from `Nat.Partrec.Code`, not from a custom Turing machine

The paper presents a universal prefix Turing machine on binary strings, but in Lean the lowest-friction starting point is mathlib's `Nat.Partrec` / `Nat.Partrec.Code` universe. That gives you:

- a universal evaluator
- code objects for programs
- existence-of-code lemmas for partial recursive functions
- a clean bridge from programs to shortest-description definitions

Then encode binary strings into naturals through standard `Encodable` machinery. This keeps the computability layer aligned with mathlib instead of fighting it.

### 3. Separate the computation model from the paper-facing API

Define the paper's objects through a thin interface:

- `BitString := List Bool`
- a length function `blen`
- pairing and self-delimiting encoding operations on `BitString`
- a universal evaluator API that looks like `U : BitString -> BitString ->. BitString`

Internally, implement this API using `Nat.Partrec.Code` and encodings to `Nat`. This gives you freedom to switch to a more explicit Turing-machine model later without rewriting the feature theory.

### 4. Expect to formalize the prefix/plain gap explicitly

The paper states results in terms of prefix Kolmogorov complexity. mathlib gives computability infrastructure, but not an off-the-shelf Kolmogorov-complexity library. So the practical route is:

- first define a description complexity over your chosen universal evaluator
- prove the feature theory against that definition
- only then decide whether to:
  - keep a plain-complexity formalization for a first end-to-end version, or
  - add a prefix-free layer and translate the main theorems

Because many statements in the paper are only up to additive logarithmic terms, a first pass with a simpler complexity notion may still capture most of the proof architecture. If you want the paper matched literally, budget separate time for the prefix-free upgrade.

### 5. Do not use informal `O(log n)` in the first implementation

The paper's proofs repeatedly hide additive constants and logarithmic slack. In Lean, informal asymptotic prose is a source of friction. Define one or two explicit relations early, for example:

- `a <=log b wrt n`
- `a ≈log b wrt n`

meaning "bounded above/below by `b + c * log (n + 1) + d` for some constants". Then state theorems with those relations instead of sprinkling ad hoc `O(log ...)` terms everywhere.

## Suggested Repository Shape

Once the Lean project exists, organize it like this:

```text
IcTheory.lean
IcTheory/
  Basics/
    BitString.lean
    Pairing.lean
    PrefixEncoding.lean
    LogBounds.lean
  Computability/
    Encodings.lean
    UniversalMachine.lean
    Search.lean
  Complexity/
    Description.lean
    Kolmogorov.lean
    Information.lean
  Compression/
    Feature.lean
    SingleStep.lean
    Iterated.lean
    BCompressible.lean
    Alice.lean
  Randomness/
    LowerSemicomputable.lean
    MartinLof.lean
    FeatureBridge.lean
docs/
  theorem-map.md
  model-decisions.md
  glossary.md
```

## Formalization Phases

### Phase 0: Setup and calibration

Deliverables:

- Lean 4 installed via `elan`
- `lake` project with mathlib
- editor support working
- one-page theorem map extracted from the paper

Concrete tasks:

1. Install Lean tooling.
2. Create a mathlib-backed project.
3. Verify `lake build` works.
4. Write a `docs/theorem-map.md` listing every definition, lemma, and theorem you intend to formalize.

Exit criterion:

You can open the project in your editor, import `Mathlib`, and compile a trivial file.

### Phase 1: Foundations the paper depends on but does not isolate

Deliverables:

- a binary-string type and its encodings
- pairing/unpairing lemmas
- self-delimiting encodings analogous to `E1` and `E2`
- the logarithmic overhead lemmas those encodings induce

Concrete tasks:

1. Define the string representation you will actually use.
2. Define the pairing scheme used in the paper, or a Lean-friendlier equivalent.
3. Prove length bounds for the encodings.
4. Decide exactly how "program length" is measured in the formalization.

Exit criterion:

You can state and prove encoding-length lemmas without mentioning compression yet.

### Phase 2: Computability substrate

Deliverables:

- a universal evaluator
- a notion of partial computable map on bitstrings
- shortest-description definitions

Concrete tasks:

1. Wrap `Nat.Partrec.Code.eval` in a paper-facing API.
2. Define conditional and unconditional description complexity.
3. Prove existence of codes and the basic "universal evaluator" lemmas.
4. Prove the minima/existence lemmas you need for "shortest program", "shortest feature", and "shortest descriptive map".

Exit criterion:

You can define `K(x | r)` and prove the existence of witnesses whenever the defining set is nonempty.

### Phase 3: Section 2 of the paper

Target statements:

- Definition 2.1
- Definition 2.2
- Lemma 2.1
- Lemma 2.2

Concrete tasks:

1. Define features, descriptive maps, residual descriptions, shortest features.
2. Formalize the compression condition.
3. Prove singleton features exist for compressible strings.
4. Prove existence of a universal feature under the stronger compressibility assumption.

Exit criterion:

All of Section 2 is formalized, with statements close to the paper.

### Phase 4: Single-step theory in Section 3.1

Target statements:

- Lemma 3.1
- Theorem 3.1
- Lemma 3.2
- Lemma 3.3
- Theorem 3.2
- Theorem 3.3
- Corollary 3.1
- Theorem 3.4

This is the technical heart of the project. It is where you should expect the most proof engineering.

Key proof-engineering tasks:

1. Package the generic complexity lemmas you repeatedly use.
2. Decide how to represent "bounded by logarithmic precision".
3. Isolate each use of information symmetry and chain rules into reusable lemmas.
4. Separate exact equalities from up-to-log statements.

Exit criterion:

You can formally derive the single-step decomposition

`K(x) ≈log K(f*) + K(r)`

and the incompressibility/independence properties needed for iteration.

### Phase 5: Iterated compression, Sections 3.2 to 3.5

Target statements:

- Lemma 3.4
- Theorem 3.5
- Theorem 3.6
- Definition 3.1
- Lemma 3.5
- Theorem 3.7
- Theorem 3.8
- Theorem 3.9

Concrete tasks:

1. Define the iterative compression chain.
2. Prove orthogonality of features.
3. Prove the near-optimality theorem for the iterated description.
4. Add the `b`-compressible variant.
5. Prove the constant-length feature bounds for well-compressible strings.

Exit criterion:

You have the main theorem architecture of the paper formalized, even if Sections 4 and 5 are still deferred.

### Phase 6: Computable algorithms, Section 4

Target statements:

- Greedy-ALICE and ALICE definitions
- Lemma 4.1
- Theorem 4.1

This phase should be deferred until the abstract theory is stable. It needs an explicit operational time model and actual search procedures, so it is a different style of formalization than the earlier AIT lemmas.

Exit criterion:

You can state ALICE as an executable or at least operational search object and prove its search-time bound.

### Phase 7: Martin-Lof randomness bridge, Section 5

Target statements:

- Definition 5.1
- Theorem 5.1
- Theorem 5.2

This is a separate mini-project inside the project. You will need:

- lower semicomputability infrastructure
- recursively enumerable sets on length slices
- cardinality bounds on test sets

Exit criterion:

You can state and prove the forward and backward bridge between features and uniform Martin-Lof tests.

## Bridging AIT Formalism vs Other Systems

This deserves its own work item, not just ad hoc translation.

### Why the gap exists

Different systems formalize algorithmic information theory with different primitives:

- explicit Turing machines
- partial recursive functions
- synthetic computability
- prefix-free machines versus plain machines

Your Lean project should not start by pretending those are interchangeable.

### Recommended bridge document

Create `docs/glossary.md` with a three-column mapping:

1. Paper notation.
2. Lean definition actually used.
3. Translation notes and proof obligations.

Initial rows should include:

- finite binary string
- program / feature / descriptive map
- universal machine
- conditional complexity `K(x | r)`
- information `I(x : y)`
- lower semicomputable randomness test
- prefix-free encoding

### Recommended comparative checkpoint

Before proving Section 3, write a short note answering:

- Are we formalizing prefix complexity directly, or a plain-complexity surrogate first?
- Which paper lemmas rely essentially on prefix-freeness?
- Which results only need a universal machine plus logarithmic slack?

If you do not answer these early, you risk having to rework the entire complexity layer later.

## Known Risk Areas

1. **Prefix complexity**: this is likely the single biggest modeling decision.
2. **Existence of minima**: every "shortest" object needs a precise Lean witness story.
3. **Log-overhead bookkeeping**: if not abstracted early, it will spread everywhere.
4. **Conditional complexity identities**: many proofs depend on small reusable inequalities.
5. **Section 5**: lower semicomputability and test counting are materially different from Sections 2 and 3.

## Practical Timeline

If you work steadily, a realistic sequence is:

- Week 1: setup, theorem map, model decisions.
- Week 2: strings, encodings, pairing, log-overhead lemmas.
- Weeks 3-4: universal evaluator and complexity definitions.
- Weeks 5-7: Section 2 plus the first half of Section 3.1.
- Weeks 8-10: Theorems 3.3 to 3.9.
- Later: ALICE and Martin-Lof randomness.

If the goal is a first credible artifact fast, stop after Phase 5. That already captures the core theory of incremental compression.

## Immediate Next Actions

1. Install Lean 4 and create a mathlib-backed project in this repository.
2. Write `docs/theorem-map.md` from the paper before proving anything.
3. Decide, in writing, whether version 1 targets plain complexity first or prefix complexity from day one.
4. Build the foundations in this order:
   - bitstrings and encodings
   - universal evaluator
   - `K(x | r)`
   - features and residuals
   - single-step theorems
   - iterated compression

## Useful References

- Lean setup and `lake`: https://docs.lean-lang.org/lean4/doc/setup.html
- Lean community project setup with mathlib: https://leanprover-community.github.io/install/project.html
- mathlib documentation index: https://leanprover-community.github.io/mathlib4_docs/Mathlib
- `Nat.Partrec.Code` docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/PartrecCode.html
- `TMComputable` docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TMComputable.html
- Coq formalization reference point: https://www.ps.uni-saarland.de/~lauermann/bachelor.php
