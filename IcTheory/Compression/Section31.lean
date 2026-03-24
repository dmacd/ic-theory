import IcTheory.Compression.Section2

namespace IcTheory

namespace Compression

open UniversalMachine

/-- The residual witness carried by a shortest descriptive map. -/
theorem exists_residual_for_shortestDescriptiveMap {f g x : Program}
    (hshort : IsShortestDescriptiveMap runs f g x) :
    ∃ r : BitString, runs g x r ∧ runs f r x ∧ CompressionCondition f r x := by
  exact hshort.1

/-- Lemma 3.1, first half: with a residual witness `r`, the shortest feature length
coincides with the conditional complexity of `x` given `r`. -/
theorem shortestFeature_eq_conditionalComplexity
    {f g x r : Program}
    (hshort : IsShortestFeature runs f x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    BitString.blen f = ConditionalComplexity x r := by
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hqLen, hqRuns⟩ := exists_program_forConditionalComplexity x r
    have hqFeature : IsFeature runs q x := by
      refine ⟨g, ?_⟩
      refine ⟨r, hr, hqRuns, ?_⟩
      have hle : BitString.blen q + BitString.blen r ≤ BitString.blen f + BitString.blen r := by
        rw [hqLen]
        exact Nat.add_le_add_right (conditionalComplexity_le_length hf) _
      exact lt_of_le_of_lt hle hcomp
    have hfg : BitString.blen f ≤ BitString.blen q := hshort.2 q hqFeature
    simpa [hqLen] using hfg
  · exact conditionalComplexity_le_length hf

/-- Lemma 3.1, second half: with a residual witness `r`, the shortest descriptive-map
length coincides with the conditional complexity of `r` given `x`. -/
theorem shortestDescriptiveMap_eq_conditionalComplexity
    {f g x r : Program}
    (hshort : IsShortestDescriptiveMap runs f g x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    BitString.blen g = ConditionalComplexity r x := by
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hqLen, hqRuns⟩ := exists_program_forConditionalComplexity r x
    have hqDesc : IsDescriptiveMap runs f q x := by
      exact ⟨r, hqRuns, hf, hcomp⟩
    have hgq : BitString.blen g ≤ BitString.blen q := hshort.2 q hqDesc
    simpa [hqLen] using hgq
  · exact conditionalComplexity_le_length hr

/-- Lemma 3.1 in a packaged form: for a shortest feature and shortest descriptive map,
some residual witness makes both lengths equal the corresponding conditional complexities. -/
theorem shortestMaps_characterize_conditionalComplexity
    {f g x : Program}
    (hshortF : IsShortestFeature runs f x)
    (hshortG : IsShortestDescriptiveMap runs f g x) :
    ∃ r : BitString,
      BitString.blen f = ConditionalComplexity x r ∧
      BitString.blen g = ConditionalComplexity r x := by
  obtain ⟨r, hr, hf, hcomp⟩ := exists_residual_for_shortestDescriptiveMap hshortG
  exact ⟨r,
    shortestFeature_eq_conditionalComplexity hshortF hr hf hcomp,
    shortestDescriptiveMap_eq_conditionalComplexity hshortG hr hf hcomp⟩

end Compression

end IcTheory
