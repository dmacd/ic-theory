# Theorem Map

## Paper

Source: `1908.03781v2.pdf`

## Section 2

- Definition 2.1: features, descriptive maps, residual descriptions, shortest features
- Definition 2.2: universal feature
- Lemma 2.1: singleton feature exists for compressible strings
- Lemma 2.2: universal feature exists for strings compressible by more than a constant

## Section 3.1

- Lemma 3.1: shortest feature and shortest descriptive map characterize conditional complexity
- Theorem 3.1: incompressibility of shortest features
- Lemma 3.2: upper bound on `K(x | f)` from a residual
- Lemma 3.3: high mutual information forces `K(f | x)` to be small
- Theorem 3.2: polynomial bound on the number of shortest features
- Theorem 3.3: general independence bound for features and residuals
- Corollary 3.1: independence for shortest features and residuals
- Theorem 3.4: no superfluous information

## Sections 3.2 to 3.5

- Lemma 3.4: auxiliary information inequality
- Theorem 3.5: orthogonality of features
- Theorem 3.6: optimality of incremental compression
- Definition 3.1: `b`-descriptive maps and `b`-features
- Lemma 3.5: transfer of main results to `b`-features
- Theorem 3.7: shortest features are constant-sized for `b`-compressible strings
- Theorem 3.8: short descriptive maps and no superfluous information in short features
- Theorem 3.9: bounds for the `b`-compressible compression scheme

## Section 4

- Greedy-ALICE definition
- ALICE definition
- Lemma 4.1: running time bound on search at a node
- Theorem 4.1: total running time / description guarantee for ALICE

Current Lean status:

- `IcTheory/Compression/Section4.lean` formalizes the fixed machine `W`, the accepted
  autoencoder-step predicate, concrete phase programs/budgets, and search-tree semantics
  (`AliceNode`, `IsAliceBranch`) for ALICE / Greedy-ALICE, together with Algorithm 2-style
  call-state/status objects (`AliceCallState`, `AliceProgramStatus`), a focused recursive-path
  container (`AliceOperationalPath`), and a global scheduler state/step model
  (`AliceSchedulerState`, `AliceSchedulerStep`, `AliceSchedulerExec`).
- Lemma 4.1 is formalized for the concrete live scheduler in
  `IcTheory/Compression/Theorem41.lean`.
- The main Section 4 theorem in `IcTheory/Compression/Theorem41.lean` now instantiates the paper's
  `t_i` and `t_i'` with actual bounded-evaluation runtimes extracted from the corresponding `runs`
  proofs, and it returns both a focused Algorithm 2-style operational path and a reachable global
  scheduler state carrying explicit status dictionaries and the branch's contribution to the global
  description list `D`.
- What is still not formalized verbatim is the exact fair phase-by-phase interleaving of every
  candidate autoencoder evaluation across all active calls.

## Section 5

- Definition 5.1: uniform Martin-Lof randomness test
- Theorem 5.1: paper-form in `IcTheory/Compression/Theorem51.lean`
- Theorem 5.2: paper-form in `IcTheory/Compression/Theorem52.lean`

## Formalization order

1. Section 2
2. Section 3.1
3. Sections 3.2 to 3.5
4. Section 4
5. Section 5
