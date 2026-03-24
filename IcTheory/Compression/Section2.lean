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

theorem universalFeature_isFeature_of_compressibleByMoreThan (x : Program)
    (hcompress : CompressibleByMoreThan universalFeatureConstant x) :
    IsFeature runs universalFeature x := by
  obtain ⟨r, hrLen, hrRuns⟩ := exists_program_forComplexity x
  refine ⟨UniversalMachine.codeToProgram (Nat.Partrec.Code.const (BitString.toNatExact r)), ?_⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · exact (UniversalMachine.runs_const_iff (BitString.toNatExact r) x r).2
      (BitString.ofNatExact_toNatExact r).symm
  · exact (UniversalMachine.runs_universalFeature_iff r x).2 hrRuns
  · simpa [CompressionCondition, CompressibleByMoreThan,
      UniversalMachine.universalFeatureConstant, hrLen, Nat.add_comm] using hcompress

theorem universalFeature_isUniversalWithConstant :
    IsUniversalFeatureWithConstant universalFeature universalFeatureConstant := by
  intro x hx
  exact universalFeature_isFeature_of_compressibleByMoreThan x hx

theorem universalFeature_isUniversal : IsUniversalFeature universalFeature := by
  exact ⟨universalFeatureConstant, universalFeature_isUniversalWithConstant⟩

theorem shortestFeature_le_universalFeatureConstant {f x : Program}
    (hshort : IsShortestFeature runs f x)
    (hcompress : CompressibleByMoreThan universalFeatureConstant x) :
    BitString.blen f ≤ universalFeatureConstant := by
  exact hshort.2 universalFeature (universalFeature_isFeature_of_compressibleByMoreThan x hcompress)

end Compression

end IcTheory
