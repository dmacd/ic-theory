import IcTheory.Compression.Theorem33

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- Corollary 3.1 equation (22) in paper form, obtained by specializing Theorem 3.3 equation (16)
to a globally shortest feature `f*`, so the gap term vanishes. -/
theorem corollary31_eq22
    {fStar g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs fStar r x)
    (hcomp : CompressionCondition fStar r x) :
    LogEq (PrefixConditionalComplexity fStar r) (PrefixComplexity fStar) (BitString.blen fStar) := by
  refine ⟨prefixConditionalComplexity_logLe_prefixComplexity fStar r, ?_⟩
  rcases theorem33_eq16 hshort hr hf hcomp with ⟨c, d, h⟩
  refine ⟨c, d, ?_⟩
  have hinfo :
      PrefixComplexity fStar - PrefixConditionalComplexity fStar r ≤
        c * logPenalty (BitString.blen fStar) + d := by
    simpa [PrefixInformation, featureGap] using h
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.sub_le_iff_le_add').1 hinfo

/-- Corollary 3.1 equation (22), reduced only to the same shortest-feature/prefix-shortest bridge
already isolated in Theorem 3.3. -/
theorem corollary31_eq22_of_prefixShortestBridge
    {fStar x r : Program}
    (hshortPrefix : BitString.blen fStar ≤ PrefixConditionalComplexity x r)
    (hf : runs fStar r x) :
    LogEq (PrefixConditionalComplexity fStar r) (PrefixComplexity fStar) (BitString.blen fStar) := by
  refine ⟨prefixConditionalComplexity_logLe_prefixComplexity fStar r, ?_⟩
  rcases theorem33_eq16_of_prefixShortestBridge
      (fStar := fStar) (f := fStar) (x := x) (r := r) hshortPrefix hf with ⟨c, d, h⟩
  refine ⟨c, d, ?_⟩
  have hinfo :
      PrefixComplexity fStar - PrefixConditionalComplexity fStar r ≤
        c * logPenalty (BitString.blen fStar) + d := by
    simpa [PrefixInformation, featureGap] using h
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.sub_le_iff_le_add').1 hinfo

/-- Shortest features satisfy the lower-bound direction of Corollary 3.1 equation (24) as an
immediate specialization of Theorem 3.3 equation (17) with gap `d = 0`. -/
theorem corollary31_eq24_lower
    {fStar g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs fStar r x)
    (hcomp : CompressionCondition fStar r x) :
    ∃ c d e : Nat,
      PrefixComplexity r + PrefixComplexity fStar ≤
        JointComplexity r fStar +
          c * logPenalty (BitString.blen fStar) +
          d * logPenalty (BitString.blen r) + e := by
  rcases theorem33_eq17 hshort hr hf hcomp with ⟨c, d, e, h⟩
  refine ⟨c, d, e, ?_⟩
  have hinfo :
      PrefixComplexity r + PrefixComplexity fStar - JointComplexity r fStar ≤
        c * logPenalty (BitString.blen fStar) +
          d * logPenalty (BitString.blen r) + e := by
    simpa [JointInformation, featureGap] using h
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.sub_le_iff_le_add').1 hinfo

/-- Shortest features satisfy the lower-bound direction of Corollary 3.1 equation (24) as an
immediate specialization of Theorem 3.3 equation (17) with gap `d = 0`. -/
theorem corollary31_eq24_lower_of_prefixShortestBridge
    {fStar x r : Program}
    (hshortPrefix : BitString.blen fStar ≤ PrefixConditionalComplexity x r)
    (hf : runs fStar r x) :
    ∃ c d e : Nat,
      PrefixComplexity r + PrefixComplexity fStar ≤
        JointComplexity r fStar +
          c * logPenalty (BitString.blen fStar) +
          d * logPenalty (BitString.blen r) + e := by
  rcases theorem33_eq17_of_prefixShortestBridge
      (fStar := fStar) (f := fStar) (x := x) (r := r) hshortPrefix hf with ⟨c, d, e, h⟩
  refine ⟨c, d, e, ?_⟩
  have hinfo :
      PrefixComplexity r + PrefixComplexity fStar - JointComplexity r fStar ≤
        c * logPenalty (BitString.blen fStar) +
          d * logPenalty (BitString.blen r) + e := by
    simpa [JointInformation, featureGap] using h
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.sub_le_iff_le_add').1 hinfo

end

end Compression

end IcTheory
