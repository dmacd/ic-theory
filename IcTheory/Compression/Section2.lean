import IcTheory.Computability.Complexity

namespace IcTheory

namespace Compression

open UniversalMachine

/-- A fixed descriptive map that always returns the empty residual. -/
def emptyDescriptiveMap : Program :=
  UniversalMachine.codeToProgram Nat.Partrec.Code.zero

/-- A universal feature with constant `C` is a feature for any string
compressible by more than `C` bits. -/
def IsUniversalFeatureWithConstant (f₀ : Program) (C : Nat) : Prop :=
  ∀ x : BitString, CompressibleByMoreThan C x → IsFeature runs f₀ x

/-- Paper Definition 2.2 specialized to the concrete universal machine. -/
def IsUniversalFeature (f₀ : Program) : Prop :=
  ∃ C : Nat, IsUniversalFeatureWithConstant f₀ C

/-- A singleton feature reconstructs `x` from the empty residual. -/
def IsSingletonFeature (f x : Program) : Prop :=
  runs f [] x ∧ BitString.blen f = Complexity x

theorem emptyDescriptiveMap_runs (x : BitString) : runs emptyDescriptiveMap x [] := by
  exact (UniversalMachine.runs_zero_iff x []).2 rfl

theorem singletonFeature_isFeature {f x : Program} (hf : IsSingletonFeature f x)
    (hcompress : Compressible x) : IsFeature runs f x := by
  refine ⟨emptyDescriptiveMap, ?_⟩
  refine ⟨[], emptyDescriptiveMap_runs x, hf.1, ?_⟩
  simpa [CompressionCondition, hf.2, Complexity, Compressible] using hcompress

theorem exists_singletonFeature (x : Program) :
    ∃ f : Program, IsSingletonFeature f x := by
  obtain ⟨f, hfLen, hfRuns⟩ := exists_program_forComplexity x
  exact ⟨f, hfRuns, hfLen⟩

theorem exists_feature_of_compressible (x : Program) (hcompress : Compressible x) :
    ∃ f : Program, IsFeature runs f x ∧ BitString.blen f = Complexity x := by
  obtain ⟨f, hf⟩ := exists_singletonFeature x
  exact ⟨f, singletonFeature_isFeature hf hcompress, hf.2⟩

theorem shortestFeature_le_complexity {f x : Program}
    (hshort : IsShortestFeature runs f x) (hcompress : Compressible x) :
    BitString.blen f ≤ Complexity x := by
  obtain ⟨g, hgFeature, hgLen⟩ := exists_feature_of_compressible x hcompress
  exact hgLen ▸ hshort.2 g hgFeature

end Compression

end IcTheory
