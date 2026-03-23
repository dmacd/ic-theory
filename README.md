# IcTheory

Lean 4 + Mathlib formalization workspace for *A theory of incremental compression*.

## Current foundation layer

- `IcTheory.Basics.BitString`: finite binary strings as `List Bool`
- `IcTheory.Basics.PrefixEncoding`: paper-style `E1` and `E2` encodings
- `IcTheory.Basics.Pairing`: prefix-based pairing and triple encoding
- `IcTheory.Basics.LogBounds`: explicit logarithmic-slack relations for later AIT theorems
- `IcTheory.Compression.Feature`: Section 2 feature/descriptive-map primitives
- `IcTheory.Computability.UniversalMachine`: exact bitstring bridge to `Nat.Partrec.Code.eval`

## Planning docs

- `PLAN.md`
- `docs/model-decisions.md`
- `docs/theorem-map.md`
