import IcTheory.Compression.Section31
import IcTheory.Computability.PrefixInformation
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- Length gap `d = l(f) - l(f*)` from Theorem 3.3. -/
def featureGap (f fStar : Program) : Nat :=
  BitString.blen f - BitString.blen fStar

/-- Any residual witness for a feature gives an upper bound on the global shortest-feature length
through the local conditional complexity `C(x | r)`. -/
theorem shortestFeature_le_conditionalComplexity_of_residual
    {fStar f g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    BitString.blen fStar ≤ ConditionalComplexity x r := by
  obtain ⟨q, hqLen, hqRuns⟩ := exists_program_forConditionalComplexity x r
  have hqFeature : IsFeature runs q x := by
    refine ⟨g, ?_⟩
    refine ⟨r, hr, hqRuns, ?_⟩
    have hle : BitString.blen q + BitString.blen r ≤ BitString.blen f + BitString.blen r := by
      rw [hqLen]
      exact Nat.add_le_add_right (conditionalComplexity_le_length hf) _
    exact lt_of_le_of_lt hle hcomp
  exact hqLen ▸ hshort.2 q hqFeature

/-- Equation (18) in additive form: `l(f)` is bounded by the global gap `d` plus the shortest
description length of `x` relative to the chosen residual `r`. -/
theorem featureLength_le_gap_add_conditionalComplexity
    {fStar f g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    BitString.blen f ≤ featureGap f fStar + ConditionalComplexity x r := by
  unfold featureGap
  have hshortLe : BitString.blen fStar ≤ ConditionalComplexity x r :=
    shortestFeature_le_conditionalComplexity_of_residual hshort hr hf hcomp
  omega

/-- Prefix complexity of `f` is bounded by the Theorem 3.3 gap plus the local conditional
complexity `C(x | r)`, up to logarithmic slack in `l(f)`. -/
theorem prefixComplexity_le_gap_add_conditionalComplexity
    {fStar f g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    LogLe (PrefixComplexity f)
      (featureGap f fStar + ConditionalComplexity x r)
      (BitString.blen f) := by
  exact logLe_trans
    (prefixComplexity_log_upper f)
    (logLe_of_le (featureLength_le_gap_add_conditionalComplexity hshort hr hf hcomp))

/-- Additive form of Theorem 3.3 equation (16), reduced to a bridge from the local plain
conditional complexity `C(x | r)` to the prefix conditional complexity `K(f | r)`. -/
theorem theorem33_eq16_additive_of_conditionalBridge
    {fStar f g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hbridge :
      LogLe (ConditionalComplexity x r) (PrefixConditionalComplexity f r) (BitString.blen f)) :
    LogLe (PrefixComplexity f)
      (featureGap f fStar + PrefixConditionalComplexity f r)
      (BitString.blen f) := by
  have hbase :
      LogLe (PrefixComplexity f)
        (featureGap f fStar + ConditionalComplexity x r)
        (BitString.blen f) :=
    prefixComplexity_le_gap_add_conditionalComplexity hshort hr hf hcomp
  have hstep :
      LogLe (featureGap f fStar + ConditionalComplexity x r)
        (featureGap f fStar + PrefixConditionalComplexity f r)
        (BitString.blen f) := by
    rcases hbridge with ⟨c, d, hcd⟩
    refine ⟨c, d, ?_⟩
    omega
  exact logLe_trans hbase hstep

/-- Theorem 3.3 equation (16) in paper-facing information form, again reduced to the missing
conditional bridge from `C(x | r)` to `K(f | r)`. -/
theorem theorem33_eq16_of_conditionalBridge
    {fStar f g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hbridge :
      LogLe (ConditionalComplexity x r) (PrefixConditionalComplexity f r) (BitString.blen f)) :
    LogLe (PrefixInformation r f) (featureGap f fStar) (BitString.blen f) := by
  rcases theorem33_eq16_additive_of_conditionalBridge hshort hr hf hcomp hbridge with ⟨c, d, h⟩
  refine ⟨c, d, ?_⟩
  unfold PrefixInformation featureGap at *
  omega

end

end Compression

end IcTheory
