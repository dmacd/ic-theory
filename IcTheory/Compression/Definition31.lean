import IcTheory.Compression.Section31

namespace IcTheory

namespace Compression

open UniversalMachine

/-- The extra residual bound in Definition 3.1: the residual is at most `|x| / b` bits long. -/
def ResidualBoundByFactor (b : Nat) (r x : Program) : Prop :=
  BitString.blen r ≤ BitString.blen x / b

/-- `g` is a `b`-descriptive map for `x` given `f` if it is descriptive in the usual sense and its
residual satisfies the additional `b`-bound. -/
def IsBDescriptiveMap (runs : Runs) (b : Nat) (f g x : Program) : Prop :=
  ∃ r : Program, runs g x r ∧ runs f r x ∧
    CompressionCondition f r x ∧ ResidualBoundByFactor b r x

/-- The set of `b`-descriptive maps of `x` given `f`. -/
def bDescriptiveMaps (runs : Runs) (b : Nat) (f x : Program) : Set Program :=
  {g | IsBDescriptiveMap runs b f g x}

/-- Residual descriptions reachable from `x` via some `b`-descriptive map for `f`. -/
def bResidualDescriptions (runs : Runs) (b : Nat) (f x : Program) : Set BitString :=
  {r | ∃ g : Program, runs g x r ∧ runs f r x ∧
    CompressionCondition f r x ∧ ResidualBoundByFactor b r x}

/-- `f` is a `b`-feature of `x` if some `b`-descriptive map exists for it. -/
def IsBFeature (runs : Runs) (b : Nat) (f x : Program) : Prop :=
  ∃ g : Program, IsBDescriptiveMap runs b f g x

/-- `f` is a shortest `b`-feature of `x` if it is a `b`-feature and no shorter `b`-feature
exists. -/
def IsShortestBFeature (runs : Runs) (b : Nat) (f x : Program) : Prop :=
  IsBFeature runs b f x ∧
    ∀ g : Program, IsBFeature runs b g x → BitString.blen f ≤ BitString.blen g

/-- `g` is a shortest `b`-descriptive map for `x` given `f` if it is `b`-descriptive and no
shorter `b`-descriptive-map program exists. -/
def IsShortestBDescriptiveMap (runs : Runs) (b : Nat) (f g x : Program) : Prop :=
  IsBDescriptiveMap runs b f g x ∧
    ∀ h : Program, IsBDescriptiveMap runs b f h x → BitString.blen g ≤ BitString.blen h

theorem isBDescriptiveMap_iff (runs : Runs) (b : Nat) (f g x : Program) :
    IsBDescriptiveMap runs b f g x ↔
      ∃ r : Program, runs g x r ∧ runs f r x ∧
        CompressionCondition f r x ∧ ResidualBoundByFactor b r x := by
  rfl

theorem mem_bDescriptiveMaps_iff (runs : Runs) (b : Nat) (f x g : Program) :
    g ∈ bDescriptiveMaps runs b f x ↔ IsBDescriptiveMap runs b f g x := by
  rfl

theorem mem_bResidualDescriptions_iff (runs : Runs) (b : Nat) (f x r : Program) :
    r ∈ bResidualDescriptions runs b f x ↔
      ∃ g : Program, runs g x r ∧ runs f r x ∧
        CompressionCondition f r x ∧ ResidualBoundByFactor b r x := by
  rfl

theorem bDescriptiveMap_forgets {runs : Runs} {b : Nat} {f g x : Program} :
    IsBDescriptiveMap runs b f g x → IsDescriptiveMap runs f g x := by
  intro h
  rcases h with ⟨r, hg, hf, hcomp, _⟩
  exact ⟨r, hg, hf, hcomp⟩

theorem bFeature_forgets {runs : Runs} {b : Nat} {f x : Program} :
    IsBFeature runs b f x → IsFeature runs f x := by
  intro h
  rcases h with ⟨g, hg⟩
  exact ⟨g, bDescriptiveMap_forgets hg⟩

theorem shortestBFeature_isBFeature {runs : Runs} {b : Nat} {f x : Program} :
    IsShortestBFeature runs b f x → IsBFeature runs b f x := by
  exact fun h => h.1

theorem shortestBFeature_forgets {runs : Runs} {b : Nat} {f x : Program} :
    IsShortestBFeature runs b f x → IsFeature runs f x := by
  exact fun h => bFeature_forgets h.1

theorem shortestBDescriptiveMap_isBDescriptiveMap {runs : Runs} {b : Nat} {f g x : Program} :
    IsShortestBDescriptiveMap runs b f g x → IsBDescriptiveMap runs b f g x := by
  exact fun h => h.1

theorem shortestBDescriptiveMap_forgets {runs : Runs} {b : Nat} {f g x : Program} :
    IsShortestBDescriptiveMap runs b f g x → IsDescriptiveMap runs f g x := by
  exact fun h => bDescriptiveMap_forgets h.1

/-- The singleton feature is automatically a `b`-feature whenever `x` is compressible, since its
residual is empty. -/
theorem singletonFeature_isBFeature {b : Nat} {f x : Program}
    (hf : IsSingletonFeature f x)
    (hcompress : Compressible x) :
    IsBFeature runs b f x := by
  refine ⟨emptyDescriptiveMap, ?_⟩
  refine ⟨[], emptyDescriptiveMap_runs x, hf.1, ?_, ?_⟩
  · simpa [CompressionCondition, hf.2, Complexity, Compressible] using hcompress
  · simp [ResidualBoundByFactor]

theorem exists_singletonBFeature (b : Nat) (x : Program)
    (hcompress : Compressible x) :
    ∃ f : Program, IsBFeature runs b f x ∧ BitString.blen f = Complexity x := by
  obtain ⟨f, hf⟩ := exists_singletonFeature x
  exact ⟨f, singletonFeature_isBFeature hf hcompress, hf.2⟩

theorem exists_bFeature_of_compressible (b : Nat) (x : Program)
    (hcompress : Compressible x) :
    ∃ f : Program, IsBFeature runs b f x ∧ BitString.blen f = Complexity x := by
  exact exists_singletonBFeature b x hcompress

theorem shortestBFeature_le_complexity {b : Nat} {f x : Program}
    (hshort : IsShortestBFeature runs b f x)
    (hcompress : Compressible x) :
    BitString.blen f ≤ Complexity x := by
  obtain ⟨g, hgFeature, hgLen⟩ := exists_bFeature_of_compressible b x hcompress
  exact hgLen ▸ hshort.2 g hgFeature

/-- The residual witness carried by a shortest `b`-descriptive map. -/
theorem exists_residual_for_shortestBDescriptiveMap {b : Nat} {f g x : Program}
    (hshort : IsShortestBDescriptiveMap runs b f g x) :
    ∃ r : Program, runs g x r ∧ runs f r x ∧
      CompressionCondition f r x ∧ ResidualBoundByFactor b r x := by
  exact hshort.1

/-- Lemma 3.1 for shortest `b`-features: with a residual witness satisfying the extra `b`-bound,
the shortest `b`-feature length still coincides with the conditional complexity of `x` given
that residual. -/
theorem shortestBFeature_eq_conditionalComplexity
    {b : Nat} {f g x r : Program}
    (hshort : IsShortestBFeature runs b f x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hres : ResidualBoundByFactor b r x) :
    BitString.blen f = ConditionalComplexity x r := by
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hqLen, hqRuns⟩ := exists_program_forConditionalComplexity x r
    have hqFeature : IsBFeature runs b q x := by
      refine ⟨g, ?_⟩
      refine ⟨r, hr, hqRuns, ?_, hres⟩
      have hle : BitString.blen q + BitString.blen r ≤ BitString.blen f + BitString.blen r := by
        rw [hqLen]
        exact Nat.add_le_add_right (conditionalComplexity_le_length hf) _
      exact lt_of_le_of_lt hle hcomp
    have hfg : BitString.blen f ≤ BitString.blen q := hshort.2 q hqFeature
    simpa [hqLen] using hfg
  · exact conditionalComplexity_le_length hf

/-- Lemma 3.1 for shortest `b`-descriptive maps: the shortest `b`-descriptive-map length
coincides with the conditional complexity of the residual given `x`. -/
theorem shortestBDescriptiveMap_eq_conditionalComplexity
    {b : Nat} {f g x r : Program}
    (hshort : IsShortestBDescriptiveMap runs b f g x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hres : ResidualBoundByFactor b r x) :
    BitString.blen g = ConditionalComplexity r x := by
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hqLen, hqRuns⟩ := exists_program_forConditionalComplexity r x
    have hqDesc : IsBDescriptiveMap runs b f q x := by
      exact ⟨r, hqRuns, hf, hcomp, hres⟩
    have hgq : BitString.blen g ≤ BitString.blen q := hshort.2 q hqDesc
    simpa [hqLen] using hgq
  · exact conditionalComplexity_le_length hr

/-- Theorem 3.1 for shortest `b`-features and shortest `b`-descriptive maps. -/
theorem shortestBMaps_characterize_conditionalComplexity
    {b : Nat} {f g x : Program}
    (hshortF : IsShortestBFeature runs b f x)
    (hshortG : IsShortestBDescriptiveMap runs b f g x) :
    ∃ r : Program,
      BitString.blen f = ConditionalComplexity x r ∧
      BitString.blen g = ConditionalComplexity r x := by
  obtain ⟨r, hr, hf, hcomp, hres⟩ := exists_residual_for_shortestBDescriptiveMap hshortG
  exact ⟨r,
    shortestBFeature_eq_conditionalComplexity hshortF hr hf hcomp hres,
    shortestBDescriptiveMap_eq_conditionalComplexity hshortG hr hf hcomp hres⟩

end Compression

end IcTheory
