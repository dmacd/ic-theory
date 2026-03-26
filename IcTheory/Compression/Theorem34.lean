import IcTheory.Compression.Corollary31
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

/-- Paper-facing prefix form of Theorem 3.4 equation (26):
the residual/feature pair can be recovered from `x` with only logarithmic advice. We encode the
pair in the project-standard order `⟨r, f⟩` so it matches `JointComplexity r f`. -/
def NoSuperfluousPair (r f x : Program) : Prop :=
  LogLe (PrefixConditionalComplexity (packedInput r f) x) 0 (BitString.blen x)

private theorem feature_length_le_of_compression {f r x : Program}
    (hcomp : CompressionCondition f r x) :
    BitString.blen f ≤ BitString.blen x := by
  unfold CompressionCondition at hcomp
  omega

private theorem residual_length_le_of_compression {f r x : Program}
    (hcomp : CompressionCondition f r x) :
    BitString.blen r ≤ BitString.blen x := by
  unfold CompressionCondition at hcomp
  omega

/-- Project the residual from a no-superfluous pair without losing more than logarithmic slack. -/
theorem noSuperfluousPair_residual {r f x : Program}
    (hpair : NoSuperfluousPair r f x) :
    LogLe (PrefixConditionalComplexity r x) 0 (BitString.blen x) := by
  have hproj :
      LogLe (PrefixConditionalComplexity r x)
        (PrefixConditionalComplexity (packedInput r f) x)
        (PrefixConditionalComplexity (packedInput r f) x) := by
    exact prefixConditionalComplexity_logLe_of_fixedConditionalPostcompose
      (u := conditionalPostComposeInterpreter)
      (g := leftPacked)
      (x := packedInput r f) (y := r) (input := x)
      conditionalPostComposeInterpreter_isConditionalPostComposeInterpreter
      (by simpa using runs_leftPacked_outer_iff x r f)
  have hpairScale :
      LogLe (PrefixConditionalComplexity (packedInput r f) x)
        (BitString.blen x)
        (BitString.blen x) := by
    exact logLe_trans hpair (logLe_of_le (Nat.zero_le _))
  exact logLe_trans (logLe_of_scale_logLe hproj hpairScale) hpair

/-- Project the feature from a no-superfluous pair without losing more than logarithmic slack. -/
theorem noSuperfluousPair_feature {r f x : Program}
    (hpair : NoSuperfluousPair r f x) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  have hproj :
      LogLe (PrefixConditionalComplexity f x)
        (PrefixConditionalComplexity (packedInput r f) x)
        (PrefixConditionalComplexity (packedInput r f) x) := by
    exact prefixConditionalComplexity_logLe_of_fixedConditionalPostcompose
      (u := conditionalPostComposeInterpreter)
      (g := rightPacked)
      (x := packedInput r f) (y := f) (input := x)
      conditionalPostComposeInterpreter_isConditionalPostComposeInterpreter
      (by simpa using runs_rightPacked_outer_iff x r f)
  have hpairScale :
      LogLe (PrefixConditionalComplexity (packedInput r f) x)
        (BitString.blen x)
        (BitString.blen x) := by
    exact logLe_trans hpair (logLe_of_le (Nat.zero_le _))
  exact logLe_trans (logLe_of_scale_logLe hproj hpairScale) hpair

/-- A no-superfluous pair is itself no more complex than `x`, up to logarithmic slack. -/
theorem pairComplexity_logLe_of_noSuperfluousPair {r f x : Program}
    (hpair : NoSuperfluousPair r f x) :
    LogLe (JointComplexity r f) (PrefixComplexity x) (BitString.blen x) := by
  let p : Program := packedInput r f
  have hscale :
      LogLe (PrefixComplexity x + PrefixConditionalComplexity p x)
        (PrefixComplexity x)
        (BitString.blen x) := by
    rcases hpair with ⟨c, d, hcd⟩
    have hpair' :
        PrefixConditionalComplexity p x ≤ c * logPenalty (BitString.blen x) + d := by
      simpa [p] using hcd
    exact ⟨c, d, by omega⟩
  have hscaleLen :
      LogLe (PrefixComplexity x + PrefixConditionalComplexity p x)
        (BitString.blen x)
        (BitString.blen x) := by
    exact logLe_trans hscale (prefixComplexity_log_upper x)
  have hupper :
      LogLe (JointComplexity x p)
        (PrefixComplexity x + PrefixConditionalComplexity p x)
        (BitString.blen x) := by
    exact logLe_of_scale_logLe
      (jointUpperChainRuleAt_complexityScale_of_interpreter
        (u := jointUpperInterpreter) (x := x) (y := p)
        jointUpperInterpreter_isJointUpperInterpreter)
      hscaleLen
  have hjoint :
      LogLe (JointComplexity x p) (PrefixComplexity x) (BitString.blen x) := by
    exact logLe_trans hupper hscale
  have hjointScale :
      LogLe (JointComplexity x p) (BitString.blen x) (BitString.blen x) := by
    exact logLe_trans hjoint (prefixComplexity_log_upper x)
  have hproj :
      LogLe (PrefixComplexity p) (JointComplexity x p) (BitString.blen x) := by
    exact logLe_of_scale_logLe (jointRightProjectionLogLe x p) hjointScale
  simpa [p, JointComplexity] using logLe_trans hproj hjoint

private theorem upperScaleLogLe_of_descriptivePair
    {f x r : Program}
    (hshortPrefix : BitString.blen f ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    LogLe (PrefixComplexity r + PrefixConditionalComplexity f r)
      (BitString.blen x)
      (BitString.blen x) := by
  have hrUpper :
      LogLe (PrefixComplexity r) (BitString.blen r) (BitString.blen x) := by
    exact logLe_of_scale_le (prefixComplexity_log_upper r)
      (residual_length_le_of_compression hcomp)
  have hfUpper :
      LogLe (PrefixComplexity f) (BitString.blen f) (BitString.blen x) := by
    exact logLe_of_scale_le (prefixComplexity_log_upper f)
      (feature_length_le_of_compression hcomp)
  have hEq22 :
      LogEq (PrefixConditionalComplexity f r) (PrefixComplexity f) (BitString.blen x) := by
    exact logEq_of_scale_le
      (corollary31_eq22_of_prefixShortestBridge hshortPrefix hf)
      (feature_length_le_of_compression hcomp)
  rcases hrUpper with ⟨c₁, d₁, h₁⟩
  rcases hEq22.1 with ⟨c₂, d₂, h₂⟩
  rcases hfUpper with ⟨c₃, d₃, h₃⟩
  have hfCond :
      PrefixConditionalComplexity f r ≤
        BitString.blen f +
          (c₂ + c₃) * logPenalty (BitString.blen x) +
          (d₂ + d₃) := by
    calc
      PrefixConditionalComplexity f r ≤
          PrefixComplexity f + c₂ * logPenalty (BitString.blen x) + d₂ := h₂
      _ ≤
          (BitString.blen f + c₃ * logPenalty (BitString.blen x) + d₃) +
            (c₂ * logPenalty (BitString.blen x) + d₂) := by
        simpa [Nat.add_assoc] using
          (Nat.add_le_add_right h₃ (c₂ * logPenalty (BitString.blen x) + d₂))
      _ =
          BitString.blen f +
            (c₂ + c₃) * logPenalty (BitString.blen x) +
            (d₂ + d₃) := by
        rw [Nat.add_mul]
        omega
  have hsum :
      PrefixComplexity r + PrefixConditionalComplexity f r ≤
        BitString.blen r + BitString.blen f +
          (c₁ + c₂ + c₃) * logPenalty (BitString.blen x) +
          (d₁ + d₂ + d₃) := by
    calc
      PrefixComplexity r + PrefixConditionalComplexity f r ≤
          (BitString.blen r + c₁ * logPenalty (BitString.blen x) + d₁) +
            PrefixConditionalComplexity f r := by
        exact Nat.add_le_add_right h₁ _
      _ ≤
          (BitString.blen r + c₁ * logPenalty (BitString.blen x) + d₁) +
            (BitString.blen f +
              (c₂ + c₃) * logPenalty (BitString.blen x) +
              (d₂ + d₃)) := by
        exact Nat.add_le_add_left hfCond _
      _ =
          BitString.blen r + BitString.blen f +
            (c₁ + c₂ + c₃) * logPenalty (BitString.blen x) +
            (d₁ + d₂ + d₃) := by
        ring_nf
  refine ⟨c₁ + c₂ + c₃, d₁ + d₂ + d₃, ?_⟩
  unfold CompressionCondition at hcomp
  have hlen : BitString.blen r + BitString.blen f ≤ BitString.blen x := by
    omega
  exact le_trans hsum (by omega)

/-- The pair `⟨r, f⟩` has the same complexity as the separate descriptions of `r` and `f`,
up to logarithmic slack, once Corollary 3.1 is available. -/
theorem jointComplexity_logLe_sum_of_prefixShortestBridge
    {f x r : Program}
    (hshortPrefix : BitString.blen f ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    LogLe (JointComplexity r f)
      (PrefixComplexity r + PrefixComplexity f)
      (BitString.blen x) := by
  have hupper :
      JointUpperChainRuleAt (BitString.blen x) r f := by
    exact jointUpperChainRuleAt_of_interpreter_of_scale_logLe
      (u := jointUpperInterpreter) (x := r) (y := f)
      jointUpperInterpreter_isJointUpperInterpreter
      (upperScaleLogLe_of_descriptivePair hshortPrefix hf hcomp)
  have hEq22 :
      LogEq (PrefixConditionalComplexity f r) (PrefixComplexity f) (BitString.blen x) := by
    exact logEq_of_scale_le
      (corollary31_eq22_of_prefixShortestBridge hshortPrefix hf)
      (feature_length_le_of_compression hcomp)
  have hstep :
      LogLe (PrefixComplexity r + PrefixConditionalComplexity f r)
        (PrefixComplexity r + PrefixComplexity f)
        (BitString.blen x) := by
    rcases hEq22.1 with ⟨c, d, hcd⟩
    exact ⟨c, d, by omega⟩
  simpa [Nat.add_comm] using logLe_trans hupper hstep

/-- Corollary 3.1 equation (24) already gives the lower direction of the separate-description
bound once its logarithmic terms are rescaled to `l(x)`. -/
theorem sumComplexity_logLe_joint_of_prefixShortestBridge
    {f x r : Program}
    (hshortPrefix : BitString.blen f ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    LogLe (PrefixComplexity f + PrefixComplexity r)
      (JointComplexity r f)
      (BitString.blen x) := by
  rcases corollary31_eq24_lower_of_prefixShortestBridge hshortPrefix hf with ⟨c, d, e, h⟩
  have hfmono :
      logPenalty (BitString.blen f) ≤ logPenalty (BitString.blen x) := by
    exact logPenalty_mono (feature_length_le_of_compression hcomp)
  have hrmono :
      logPenalty (BitString.blen r) ≤ logPenalty (BitString.blen x) := by
    exact logPenalty_mono (residual_length_le_of_compression hcomp)
  have h' :
      PrefixComplexity r + PrefixComplexity f ≤
        JointComplexity r f + (c + d) * logPenalty (BitString.blen x) + e := by
    calc
      PrefixComplexity r + PrefixComplexity f ≤
          JointComplexity r f +
            c * logPenalty (BitString.blen f) +
            d * logPenalty (BitString.blen r) + e := h
      _ ≤
          JointComplexity r f +
            c * logPenalty (BitString.blen x) +
            d * logPenalty (BitString.blen x) + e := by
        have hc :
            c * logPenalty (BitString.blen f) ≤
              c * logPenalty (BitString.blen x) := Nat.mul_le_mul_left _ hfmono
        have hd :
            d * logPenalty (BitString.blen r) ≤
              d * logPenalty (BitString.blen x) := Nat.mul_le_mul_left _ hrmono
        omega
      _ = JointComplexity r f + (c + d) * logPenalty (BitString.blen x) + e := by
        rw [Nat.add_mul]
        omega
  refine ⟨c + d, e, ?_⟩
  calc
    PrefixComplexity f + PrefixComplexity r =
        PrefixComplexity r + PrefixComplexity f := by omega
    _ ≤ JointComplexity r f + (c + d) * logPenalty (BitString.blen x) + e := h'

/-- Theorem 3.4 equation (27), reduced to the remaining bridge from plain residual complexity to
its prefix version. -/
theorem theorem34_eq27_of_noSuperfluousPair_and_conditionalBridge
    {f g x r : Program}
    (hshort : IsShortestDescriptiveMap runs f g x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hpair : NoSuperfluousPair r f x)
    (hbridge :
      LogLe (ConditionalComplexity r x) (PrefixConditionalComplexity r x) (BitString.blen x)) :
    LogLe (BitString.blen g) 0 (BitString.blen x) := by
  have hlen : BitString.blen g = ConditionalComplexity r x :=
    shortestDescriptiveMap_eq_conditionalComplexity hshort hr hf hcomp
  rw [hlen]
  exact logLe_trans hbridge (noSuperfluousPair_residual hpair)

/-- Theorem 3.4 equation (28), upper direction:
`K(x) ≤ K(f) + K(r) + O(log l(x))`. -/
theorem theorem34_eq28_upper_of_prefixShortestBridge_and_noSuperfluousPair
    {f x r : Program}
    (hshortPrefix : BitString.blen f ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (_hpair : NoSuperfluousPair r f x) :
    LogLe (PrefixComplexity x)
      (PrefixComplexity f + PrefixComplexity r)
      (BitString.blen x) := by
  have hrUpper :
      LogLe (PrefixComplexity r) (BitString.blen r) (BitString.blen x) := by
    exact logLe_of_scale_le (prefixComplexity_log_upper r)
      (residual_length_le_of_compression hcomp)
  have hfx :
      LogLe (PrefixConditionalComplexity x r) (PrefixConditionalComplexity f r) (BitString.blen x) := by
    exact logLe_of_scale_le (prefixConditionalComplexity_logLe_of_runs hf)
      (feature_length_le_of_compression hcomp)
  have hEq22 :
      LogEq (PrefixConditionalComplexity f r) (PrefixComplexity f) (BitString.blen x) := by
    exact logEq_of_scale_le
      (corollary31_eq22_of_prefixShortestBridge hshortPrefix hf)
      (feature_length_le_of_compression hcomp)
  have hfUpper :
      LogLe (PrefixComplexity f) (BitString.blen f) (BitString.blen x) := by
    exact logLe_of_scale_le (prefixComplexity_log_upper f)
      (feature_length_le_of_compression hcomp)
  have hxUpper :
      LogLe (PrefixConditionalComplexity x r) (BitString.blen f) (BitString.blen x) := by
    exact logLe_trans hfx (logLe_trans hEq22.1 hfUpper)
  have hscale :
      LogLe (PrefixComplexity r + PrefixConditionalComplexity x r)
        (BitString.blen x)
        (BitString.blen x) := by
    rcases hrUpper with ⟨c₁, d₁, h₁⟩
    rcases hxUpper with ⟨c₂, d₂, h₂⟩
    have hsum :
        PrefixComplexity r + PrefixConditionalComplexity x r ≤
          BitString.blen r + BitString.blen f +
            (c₁ + c₂) * logPenalty (BitString.blen x) + (d₁ + d₂) := by
      calc
        PrefixComplexity r + PrefixConditionalComplexity x r ≤
            (BitString.blen r + c₁ * logPenalty (BitString.blen x) + d₁) +
              (BitString.blen f + c₂ * logPenalty (BitString.blen x) + d₂) := by
          exact Nat.add_le_add h₁ h₂
        _ =
            BitString.blen r + BitString.blen f +
              (c₁ + c₂) * logPenalty (BitString.blen x) + (d₁ + d₂) := by
          rw [Nat.add_mul]
          omega
    refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
    unfold CompressionCondition at hcomp
    have hlen : BitString.blen r + BitString.blen f ≤ BitString.blen x := by
      omega
    exact le_trans hsum (by omega)
  have hupper :
      JointUpperChainRuleAt (BitString.blen x) r x := by
    exact jointUpperChainRuleAt_of_interpreter_of_scale_logLe
      (u := jointUpperInterpreter) (x := r) (y := x)
      jointUpperInterpreter_isJointUpperInterpreter hscale
  have hjointScale :
      LogLe (JointComplexity r x) (BitString.blen x) (BitString.blen x) := by
    exact logLe_trans hupper hscale
  have hproj :
      LogLe (PrefixComplexity x) (JointComplexity r x) (BitString.blen x) := by
    exact logLe_of_scale_logLe (jointRightProjectionLogLe r x) hjointScale
  have hxCond :
      LogLe (PrefixComplexity x)
        (PrefixComplexity r + PrefixConditionalComplexity x r)
        (BitString.blen x) := by
    exact logLe_trans hproj hupper
  have hstep₁ :
      LogLe (PrefixComplexity r + PrefixConditionalComplexity x r)
        (PrefixComplexity r + PrefixConditionalComplexity f r)
        (BitString.blen x) := by
    rcases hfx with ⟨c, d, hcd⟩
    exact ⟨c, d, by omega⟩
  have hstep₂ :
      LogLe (PrefixComplexity r + PrefixConditionalComplexity f r)
        (PrefixComplexity r + PrefixComplexity f)
        (BitString.blen x) := by
    rcases hEq22.1 with ⟨c, d, hcd⟩
    exact ⟨c, d, by omega⟩
  simpa [Nat.add_comm] using logLe_trans hxCond (logLe_trans hstep₁ hstep₂)

/-- Theorem 3.4 equation (28), lower direction:
`K(f) + K(r) ≤ K(x) + O(log l(x))`. -/
theorem theorem34_eq28_lower_of_prefixShortestBridge_and_noSuperfluousPair
    {f x r : Program}
    (hshortPrefix : BitString.blen f ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hpair : NoSuperfluousPair r f x) :
    LogLe (PrefixComplexity f + PrefixComplexity r)
      (PrefixComplexity x)
      (BitString.blen x) := by
  have hsum :
      LogLe (PrefixComplexity f + PrefixComplexity r)
        (JointComplexity r f)
        (BitString.blen x) :=
    sumComplexity_logLe_joint_of_prefixShortestBridge hshortPrefix hf hcomp
  exact logLe_trans hsum (pairComplexity_logLe_of_noSuperfluousPair hpair)

/-- Theorem 3.4 equation (28), reduced to the no-superfluous-pair witness from equation (26). -/
theorem theorem34_eq28_of_prefixShortestBridge_and_noSuperfluousPair
    {f x r : Program}
    (hshortPrefix : BitString.blen f ≤ PrefixConditionalComplexity x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hpair : NoSuperfluousPair r f x) :
    LogEq (PrefixComplexity x)
      (PrefixComplexity f + PrefixComplexity r)
      (BitString.blen x) := by
  refine ⟨theorem34_eq28_upper_of_prefixShortestBridge_and_noSuperfluousPair
      hshortPrefix hf hcomp hpair, ?_⟩
  exact theorem34_eq28_lower_of_prefixShortestBridge_and_noSuperfluousPair
    hshortPrefix hf hcomp hpair

end

end Compression

end IcTheory
