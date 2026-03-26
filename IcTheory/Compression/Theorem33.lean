import IcTheory.Compression.Section31
import IcTheory.Computability.SymmetryOfInformation
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- Length gap `d = l(f) - l(f*)` from Theorem 3.3. -/
def featureGap (f fStar : Program) : Nat :=
  BitString.blen f - BitString.blen fStar

/-- Prefix/joint version of the paper's left-hand side `K(r) + K(f) - K(f, r)`.
We use the ordered joint encoding `packedInput r f`; swap invariance is already available up to the
same logarithmic precision. -/
def JointInformation (r f : Program) : Nat :=
  PrefixComplexity r + PrefixComplexity f - JointComplexity r f

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

/-- Prefix-facing residual bridge: if the shortest feature is already bounded by the prefix
conditional complexity of `x` given `r`, then the same length-gap argument is available entirely
inside the prefix layer. -/
theorem featureLength_le_gap_add_prefixConditionalComplexity
    {fStar f x r : Program}
    (hshortPrefix : BitString.blen fStar ≤ PrefixConditionalComplexity x r) :
    BitString.blen f ≤ featureGap f fStar + PrefixConditionalComplexity x r := by
  unfold featureGap
  omega

/-- Prefix complexity of `f` is bounded by the Theorem 3.3 gap plus the prefix conditional
complexity of `x` given `r`, up to logarithmic slack in `l(f)`. -/
theorem prefixComplexity_le_gap_add_prefixConditionalComplexity
    {fStar f x r : Program}
    (hshortPrefix : BitString.blen fStar ≤ PrefixConditionalComplexity x r) :
    LogLe (PrefixComplexity f)
      (featureGap f fStar + PrefixConditionalComplexity x r)
      (BitString.blen f) := by
  exact logLe_trans
    (prefixComplexity_log_upper f)
    (logLe_of_le (featureLength_le_gap_add_prefixConditionalComplexity hshortPrefix))

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

/-- Theorem 3.3 equation (16), now reduced only to the remaining formalism gap between shortest
features and prefix descriptions of `x` given the residual `r`. The right-hand bridge
`K(x | r) ≤ K(f | r) + O(log l(f))` is proved concretely from `runs f r x`. -/
theorem theorem33_eq16_additive_of_prefixShortestBridge
    {fStar f x r : Program}
    (hshortPrefix : BitString.blen fStar ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x) :
    LogLe (PrefixComplexity f)
      (featureGap f fStar + PrefixConditionalComplexity f r)
      (BitString.blen f) := by
  have hbase :
      LogLe (PrefixComplexity f)
        (featureGap f fStar + PrefixConditionalComplexity x r)
        (BitString.blen f) :=
    prefixComplexity_le_gap_add_prefixConditionalComplexity hshortPrefix
  have hstep :
      LogLe (featureGap f fStar + PrefixConditionalComplexity x r)
        (featureGap f fStar + PrefixConditionalComplexity f r)
        (BitString.blen f) := by
    rcases prefixConditionalComplexity_logLe_of_runs hf with ⟨c, d, hcd⟩
    refine ⟨c, d, ?_⟩
    omega
  exact logLe_trans hbase hstep

/-- Paper-facing information form of Theorem 3.3 equation (16), reduced to the single remaining
shortest-feature/prefix-description bridge. -/
theorem theorem33_eq16_of_prefixShortestBridge
    {fStar f x r : Program}
    (hshortPrefix : BitString.blen fStar ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x) :
    LogLe (PrefixInformation r f) (featureGap f fStar) (BitString.blen f) := by
  rcases theorem33_eq16_additive_of_prefixShortestBridge hshortPrefix hf with ⟨c, d, h⟩
  refine ⟨c, d, ?_⟩
  unfold PrefixInformation featureGap at *
  omega

private theorem blen_packedInput_le_lengthSum (r f : Program) :
    BitString.blen (packedInput r f) ≤ 2 * (BitString.blen r + BitString.blen f + 1) := by
  unfold packedInput
  refine le_trans (BitString.blen_ofNatExact_le_size _) ?_
  let a := BitString.toNatExact r
  let b := BitString.toNatExact f
  let m := max (BitString.blen r + 1) (BitString.blen f + 1)
  have ha : a < 2 ^ m := by
    exact lt_of_lt_of_le
      (BitString.toNatExact_lt_two_pow_succ_blen r)
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hb : b < 2 ^ m := by
    exact lt_of_lt_of_le
      (BitString.toNatExact_lt_two_pow_succ_blen f)
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hmax : max a b + 1 ≤ 2 ^ m := by
    exact Nat.succ_le_of_lt (max_lt_iff.mpr ⟨ha, hb⟩)
  have hpair :
      Nat.pair a b < 2 ^ (2 * m) := by
    refine lt_of_lt_of_le (Nat.pair_lt_max_add_one_sq a b) ?_
    have hsq : (max a b + 1) ^ 2 ≤ (2 ^ m) ^ 2 := by
      rw [pow_two, pow_two]
      exact Nat.mul_le_mul hmax hmax
    simpa [pow_two, show 2 * m = m + m by omega, Nat.pow_add] using hsq
  have hsize : Nat.size (Nat.pair a b) ≤ 2 * m := by
    exact (Nat.size_le).2 hpair
  have hm : 2 * m ≤ 2 * (BitString.blen r + BitString.blen f + 1) := by
    refine Nat.mul_le_mul_left 2 ?_
    refine max_le ?_ ?_
    · omega
    · omega
  exact le_trans hsize hm

private theorem jointComplexity_le_linear_lengthSum (r f : Program) :
    JointComplexity r f ≤
      6 * (BitString.blen r + BitString.blen f + 1) + rightInterpreterPrefixOverhead := by
  have hbase :
      JointComplexity r f ≤
        BitString.blen (packedInput r f) +
          2 * BitString.blen (BitString.ofNat (BitString.blen (packedInput r f))) +
          rightInterpreterPrefixOverhead := by
    simpa [JointComplexity, PrefixComplexity] using
      (prefixConditionalComplexity_le_rightPayload (packedInput r f) ([] : Program))
  have henc :
      BitString.blen (BitString.ofNat (BitString.blen (packedInput r f))) ≤
        BitString.blen (packedInput r f) := by
    exact BitString.blen_ofNat_le_self (BitString.blen (packedInput r f))
  have hpack := blen_packedInput_le_lengthSum r f
  omega

private theorem jointComplexity_logPenalty_le_lengths (r f : Program) :
    logPenalty (JointComplexity r f) ≤
      logPenalty (BitString.blen r) + logPenalty (BitString.blen f) +
        (rightInterpreterPrefixOverhead + 8) := by
  let s : Nat := BitString.blen r + BitString.blen f
  have hlin :
      JointComplexity r f ≤ 6 * (s + 1) + rightInterpreterPrefixOverhead := by
    simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      jointComplexity_le_linear_lengthSum r f
  let a : Nat := 2 ^ (rightInterpreterPrefixOverhead + 7)
  have ha : rightInterpreterPrefixOverhead + 7 ≤ a := by
    dsimp [a]
    exact Nat.le_of_lt
      (show rightInterpreterPrefixOverhead + 7 < 2 ^ (rightInterpreterPrefixOverhead + 7) from
        Nat.lt_two_pow_self)
  have hpoly :
      6 * (s + 1) + rightInterpreterPrefixOverhead ≤
        (s + 1) * 2 ^ (rightInterpreterPrefixOverhead + 7) - 1 := by
    have hscale :
        rightInterpreterPrefixOverhead ≤ rightInterpreterPrefixOverhead * (s + 1) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.mul_le_mul_left rightInterpreterPrefixOverhead (show 1 ≤ s + 1 by omega))
    have hbase :
        6 * (s + 1) + rightInterpreterPrefixOverhead ≤
          (rightInterpreterPrefixOverhead + 7) * (s + 1) - 1 := by
      have hsucc :
          6 * (s + 1) + rightInterpreterPrefixOverhead <
            6 * (s + 1) + rightInterpreterPrefixOverhead + 1 := by
        exact Nat.lt_succ_self _
      have hsum :
          6 * (s + 1) + rightInterpreterPrefixOverhead + 1 ≤
            rightInterpreterPrefixOverhead * (s + 1) + 7 * (s + 1) := by
        omega
      have hlt :
          6 * (s + 1) + rightInterpreterPrefixOverhead <
            (rightInterpreterPrefixOverhead + 7) * (s + 1) := by
        have hsum' :
            6 * (s + 1) + rightInterpreterPrefixOverhead + 1 ≤
              (rightInterpreterPrefixOverhead + 7) * (s + 1) := by
          calc
            6 * (s + 1) + rightInterpreterPrefixOverhead + 1 ≤
                rightInterpreterPrefixOverhead * (s + 1) + 7 * (s + 1) := hsum
            _ = (rightInterpreterPrefixOverhead + 7) * (s + 1) := by
              rw [Nat.add_mul]
        refine lt_of_lt_of_le hsucc ?_
        exact hsum'
      exact Nat.le_pred_of_lt hlt
    have hmul :
        (rightInterpreterPrefixOverhead + 7) * (s + 1) ≤
          (s + 1) * 2 ^ (rightInterpreterPrefixOverhead + 7) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, a] using
        Nat.mul_le_mul_right (s + 1) ha
    exact le_trans hbase (Nat.sub_le_sub_right hmul 1)
  have hjoint :
      JointComplexity r f ≤ (s + 1) * 2 ^ (rightInterpreterPrefixOverhead + 7) - 1 := by
    exact le_trans hlin hpoly
  have hscale :
      logPenalty (JointComplexity r f) ≤ logPenalty s + (rightInterpreterPrefixOverhead + 7) := by
    exact logPenalty_le_of_le_twoPow_mul_succ_sub_one (n := s)
      (k := rightInterpreterPrefixOverhead + 7) hjoint
  have hadd :
      logPenalty s ≤ logPenalty (BitString.blen r) + logPenalty (BitString.blen f) + 1 := by
    simpa [s, Nat.add_comm] using logPenalty_add_le (BitString.blen r) (BitString.blen f)
  calc
    logPenalty (JointComplexity r f) ≤ logPenalty s + (rightInterpreterPrefixOverhead + 7) := hscale
    _ ≤
        (logPenalty (BitString.blen r) + logPenalty (BitString.blen f) + 1) +
          (rightInterpreterPrefixOverhead + 7) := by
      exact Nat.add_le_add_right hadd _
    _ = logPenalty (BitString.blen r) + logPenalty (BitString.blen f) +
          (rightInterpreterPrefixOverhead + 8) := by
      omega

private theorem jointInformation_le_prefixInformation_add_lengthLogs (r f : Program) :
    ∃ c d e : Nat,
      JointInformation r f ≤
        PrefixInformation r f +
          c * logPenalty (BitString.blen f) +
          d * logPenalty (BitString.blen r) + e := by
  rcases jointLowerChainRuleAt_concrete_of_scale_le (x := r) (y := f) (n := JointComplexity r f)
      le_rfl with ⟨c, d, hlower⟩
  have hjoint :=
    jointComplexity_logPenalty_le_lengths r f
  refine ⟨c, c, c * (rightInterpreterPrefixOverhead + 8) + d, ?_⟩
  have hlogmul :
      c * logPenalty (JointComplexity r f) ≤
        c *
          (logPenalty (BitString.blen r) + logPenalty (BitString.blen f) +
            (rightInterpreterPrefixOverhead + 8)) := by
    exact Nat.mul_le_mul_left c hjoint
  have hlower' :
      PrefixComplexity r + PrefixConditionalComplexity f r ≤
        JointComplexity r f +
          (c * logPenalty (BitString.blen f) + c * logPenalty (BitString.blen r) +
            (c * (rightInterpreterPrefixOverhead + 8) + d)) := by
    calc
      PrefixComplexity r + PrefixConditionalComplexity f r ≤
          JointComplexity r f + c * logPenalty (JointComplexity r f) + d := hlower
      _ ≤
          JointComplexity r f +
            c *
              (logPenalty (BitString.blen r) + logPenalty (BitString.blen f) +
                (rightInterpreterPrefixOverhead + 8)) + d := by
        have haux :
            c * logPenalty (JointComplexity r f) + d ≤
              c *
                (logPenalty (BitString.blen r) + logPenalty (BitString.blen f) +
                  (rightInterpreterPrefixOverhead + 8)) + d := by
          exact Nat.add_le_add_right hlogmul d
        have haux' :
            JointComplexity r f + (c * logPenalty (JointComplexity r f) + d) ≤
              JointComplexity r f +
                (c *
                  (logPenalty (BitString.blen r) + logPenalty (BitString.blen f) +
                    (rightInterpreterPrefixOverhead + 8)) + d) := by
          exact Nat.add_le_add_left haux _
        simpa [Nat.add_assoc] using haux'
      _ =
          JointComplexity r f +
            (c * logPenalty (BitString.blen f) + c * logPenalty (BitString.blen r) +
              (c * (rightInterpreterPrefixOverhead + 8) + d)) := by
        rw [Nat.mul_add, Nat.mul_add]
        omega
  have hsplit :
      PrefixComplexity f ≤ PrefixConditionalComplexity f r + PrefixInformation r f := by
    unfold PrefixInformation
    by_cases hfr : PrefixConditionalComplexity f r ≤ PrefixComplexity f
    · rw [Nat.add_sub_of_le hfr]
    · have hrf : PrefixComplexity f ≤ PrefixConditionalComplexity f r := Nat.le_of_not_ge hfr
      rw [Nat.sub_eq_zero_of_le hrf]
      exact hrf
  have hsum :
      PrefixComplexity r + PrefixComplexity f ≤
        JointComplexity r f +
          (PrefixInformation r f +
            (c * logPenalty (BitString.blen f) + c * logPenalty (BitString.blen r) +
              (c * (rightInterpreterPrefixOverhead + 8) + d))) := by
    calc
      PrefixComplexity r + PrefixComplexity f ≤
          PrefixComplexity r + (PrefixConditionalComplexity f r + PrefixInformation r f) := by
        exact Nat.add_le_add_left hsplit _
      _ = PrefixComplexity r + PrefixConditionalComplexity f r + PrefixInformation r f := by
        ac_rfl
      _ ≤
          (JointComplexity r f +
            (c * logPenalty (BitString.blen f) + c * logPenalty (BitString.blen r) +
              (c * (rightInterpreterPrefixOverhead + 8) + d))) +
            PrefixInformation r f := by
        exact Nat.add_le_add_right hlower' _
      _ =
          JointComplexity r f +
            (PrefixInformation r f +
              (c * logPenalty (BitString.blen f) + c * logPenalty (BitString.blen r) +
                (c * (rightInterpreterPrefixOverhead + 8) + d))) := by
        omega
  unfold JointInformation
  exact (Nat.sub_le_iff_le_add').2 (by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum)

/-- Equation (17) reduced to equation (16): the concrete lower chain rule converts the pair
information `K(r) + K(f) - K(r, f)` into `K(f) - K(f | r)` plus only logarithmic overhead in the
lengths of `f` and `r`. -/
theorem theorem33_eq17_additive_of_eq16
    {fStar f r : Program}
    (heq16 : LogLe (PrefixInformation r f) (featureGap f fStar) (BitString.blen f)) :
    ∃ c d e : Nat,
      JointInformation r f ≤
        featureGap f fStar +
          c * logPenalty (BitString.blen f) +
          d * logPenalty (BitString.blen r) + e := by
  rcases heq16 with ⟨c₁, d₁, h₁⟩
  rcases jointInformation_le_prefixInformation_add_lengthLogs r f with ⟨c₂, d₂, e₂, h₂⟩
  refine ⟨c₁ + c₂, d₂, d₁ + e₂, ?_⟩
  let extra : Nat :=
    c₂ * logPenalty (BitString.blen f) + d₂ * logPenalty (BitString.blen r) + e₂
  have h₁' :
      PrefixInformation r f + extra ≤
        (featureGap f fStar + c₁ * logPenalty (BitString.blen f) + d₁) + extra := by
    exact Nat.add_le_add_right h₁ extra
  calc
    JointInformation r f ≤
        PrefixInformation r f +
          c₂ * logPenalty (BitString.blen f) +
          d₂ * logPenalty (BitString.blen r) + e₂ := h₂
    _ ≤
        (featureGap f fStar + c₁ * logPenalty (BitString.blen f) + d₁) +
          (c₂ * logPenalty (BitString.blen f) +
            d₂ * logPenalty (BitString.blen r) + e₂) := by
      simpa [extra, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₁'
    _ =
        featureGap f fStar +
          (c₁ + c₂) * logPenalty (BitString.blen f) +
          d₂ * logPenalty (BitString.blen r) + (d₁ + e₂) := by
      rw [Nat.add_mul]
      omega

/-- Theorem 3.3 equation (17), reduced to the same plain-to-prefix bridge as equation (16). -/
theorem theorem33_eq17_of_conditionalBridge
    {fStar f g x r : Program}
    (hshort : IsShortestFeature runs fStar x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hbridge :
      LogLe (ConditionalComplexity x r) (PrefixConditionalComplexity f r) (BitString.blen f)) :
    ∃ c d e : Nat,
      JointInformation r f ≤
        featureGap f fStar +
          c * logPenalty (BitString.blen f) +
          d * logPenalty (BitString.blen r) + e := by
  exact theorem33_eq17_additive_of_eq16
    (theorem33_eq16_of_conditionalBridge hshort hr hf hcomp hbridge)

/-- Theorem 3.3 equation (17), now reduced only to the remaining shortest-feature versus
prefix-shortest gap already isolated by equation (16). -/
theorem theorem33_eq17_of_prefixShortestBridge
    {fStar f x r : Program}
    (hshortPrefix : BitString.blen fStar ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x) :
    ∃ c d e : Nat,
      JointInformation r f ≤
        featureGap f fStar +
          c * logPenalty (BitString.blen f) +
          d * logPenalty (BitString.blen r) + e := by
  exact theorem33_eq17_additive_of_eq16
    (theorem33_eq16_of_prefixShortestBridge hshortPrefix hf)

end

end Compression

end IcTheory
