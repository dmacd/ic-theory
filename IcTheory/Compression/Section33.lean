import IcTheory.Compression.Section32
import IcTheory.Computability.PrefixInformation
import IcTheory.Computability.SymmetryOfInformation

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- Additive form of the paper's hypothesis
`I(f : x) ≥ l(f) - O(log l(x))`.
We use this form because `Nat` subtraction truncates. -/
def HighInformationIn (f x : Program) : Prop :=
  LogLe (BitString.blen f + PrefixConditionalComplexity x f)
    (PrefixComplexity x)
    (BitString.blen x)

/-- Additive form of the one-sided symmetry-of-information inequality
`I(f : x) ≤ I(x : f) + O(log l(x))`. -/
def SymmetricInformationBound (f x : Program) : Prop :=
  LogLe (PrefixComplexity x + PrefixConditionalComplexity f x)
    (PrefixComplexity f + PrefixConditionalComplexity x f)
    (BitString.blen x)

/-- SoI at the paper's scale `l(x)`, decomposed into the standard joint-complexity ingredients. -/
def JointRulesAtFeatureScale (f x : Program) : Prop :=
  JointLowerChainRuleAt (BitString.blen x) x f ∧
    JointSwapInvariantAt (BitString.blen x) x f ∧
    JointUpperChainRuleAt (BitString.blen x) f x

theorem symmetricInformationBound_of_jointRules {f x : Program}
    (hjoint : JointRulesAtFeatureScale f x) :
    SymmetricInformationBound f x := by
  exact symmetricInformationBound_of_jointRulesAt hjoint.1 hjoint.2.1 hjoint.2.2

/-- A fixed upper-chain interpreter gives the Section 3.3 upper-chain hypothesis as soon as the
natural complexity scale is known to lie below `l(x)`. -/
theorem jointUpperAtFeatureScale_of_interpreter {u f x : Program}
    (hu : IsJointUpperInterpreter u)
    (hscale : PrefixComplexity f + PrefixConditionalComplexity x f ≤ BitString.blen x) :
    JointUpperChainRuleAt (BitString.blen x) f x := by
  exact jointUpperChainRuleAt_of_interpreter_of_scale_le hu hscale

/-- The Section 3.3 upper-chain hypothesis from the concrete fixed interpreter. -/
theorem jointUpperAtFeatureScale {f x : Program}
    (hscale : PrefixComplexity f + PrefixConditionalComplexity x f ≤ BitString.blen x) :
    JointUpperChainRuleAt (BitString.blen x) f x := by
  exact jointUpperAtFeatureScale_of_interpreter jointUpperInterpreter_isJointUpperInterpreter hscale

/-- The Section 3.3 lower-chain hypothesis from a sharp fixed-`x` count bound at the natural
joint-complexity scale. The projection and header terms are now handled internally. -/
theorem jointLowerAtFeatureScale_of_jointRightCountBound {u f x : Program}
    (hu : IsJointRightEnumerator u)
    (hcount : JointRightCountBoundAt (JointComplexity x f) x f)
    (hscale : JointComplexity x f ≤ BitString.blen x) :
    JointLowerChainRuleAt (BitString.blen x) x f := by
  exact jointLowerChainRuleAt_of_jointRightCountBoundAt_of_leftProjection_of_scale_le
    (u := u) (x := x) (y := f) hu hcount hscale

/-- Concrete sufficient conditions for the full Section 3.3 joint-rule package. -/
theorem jointRulesAtFeatureScale_of_jointRightCountBound {u f x : Program}
    (hu : IsJointRightEnumerator u)
    (hcount : JointRightCountBoundAt (JointComplexity x f) x f)
    (hlowerScale : JointComplexity x f ≤ BitString.blen x)
    (hswapScale : JointComplexity f x ≤ BitString.blen x)
    (hupperScale : PrefixComplexity f + PrefixConditionalComplexity x f ≤ BitString.blen x) :
    JointRulesAtFeatureScale f x := by
  refine ⟨?_, ?_, ?_⟩
  · exact jointLowerAtFeatureScale_of_jointRightCountBound (u := u) (f := f) (x := x)
      hu hcount hlowerScale
  · exact jointSwapInvariantAt_of_bounds hlowerScale hswapScale
  · exact jointUpperAtFeatureScale hupperScale

/-- Concrete sufficient conditions for the Section 3.3 lower-chain hypothesis using both
enumerators directly: the right-family enumerator feeds the lower-chain machine argument, and the
left-family enumerator discharges the sharp count bound. -/
theorem jointLowerAtFeatureScale_of_jointCountEnumerators {u v f x : Program}
    (hu : IsJointRightEnumerator u)
    (hv : IsJointLeftCountEnumerator v)
    (hscale : JointComplexity x f ≤ BitString.blen x) :
    JointLowerChainRuleAt (BitString.blen x) x f := by
  exact jointLowerAtFeatureScale_of_jointRightCountBound
    (u := u) (f := f) (x := x) hu
    (jointRightCountBoundAt_of_jointLeftCountEnumerator
      (u := v) (x := x) (y := f) (n := JointComplexity x f) hv)
    hscale

/-- Concrete sufficient conditions for the full Section 3.3 joint-rule package using the two
enumerators directly. -/
theorem jointRulesAtFeatureScale_of_jointCountEnumerators {u v f x : Program}
    (hu : IsJointRightEnumerator u)
    (hv : IsJointLeftCountEnumerator v)
    (hlowerScale : JointComplexity x f ≤ BitString.blen x)
    (hswapScale : JointComplexity f x ≤ BitString.blen x)
    (hupperScale : PrefixComplexity f + PrefixConditionalComplexity x f ≤ BitString.blen x) :
    JointRulesAtFeatureScale f x := by
  refine ⟨?_, ?_, ?_⟩
  · exact jointLowerAtFeatureScale_of_jointCountEnumerators
      (u := u) (v := v) (f := f) (x := x) hu hv hlowerScale
  · exact jointSwapInvariantAt_of_bounds hlowerScale hswapScale
  · exact jointUpperAtFeatureScale hupperScale

/-- Lemma 3.3 reduced to a symmetry-of-information hypothesis over the prefix layer. -/
theorem lemma33_of_symmetry {f x : Program}
    (hfeature : IsFeature runs f x)
    (hinfo : HighInformationIn f x)
    (hsymm : SymmetricInformationBound f x) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  obtain ⟨c₁, d₁, h₁⟩ := hinfo
  obtain ⟨c₂, d₂, h₂⟩ := hsymm
  have hlen : BitString.blen f ≤ BitString.blen x := (feature_length_lt hfeature).le
  obtain ⟨c₃, d₃, h₃⟩ := prefixComplexity_log_upper_of_le (x := f) hlen
  have h12 :
      BitString.blen f + PrefixConditionalComplexity f x ≤
        PrefixComplexity f +
          (c₁ * logPenalty (BitString.blen x) + d₁) +
          (c₂ * logPenalty (BitString.blen x) + d₂) := by
    omega
  have h123 :
      BitString.blen f + PrefixConditionalComplexity f x ≤
        BitString.blen f +
          ((c₁ * logPenalty (BitString.blen x) + d₁) +
            (c₂ * logPenalty (BitString.blen x) + d₂)) +
          (c₃ * logPenalty (BitString.blen x) + d₃) := by
    omega
  have hk :
      PrefixConditionalComplexity f x ≤
        ((c₁ * logPenalty (BitString.blen x) + d₁) +
          (c₂ * logPenalty (BitString.blen x) + d₂)) +
        (c₃ * logPenalty (BitString.blen x) + d₃) := by
    omega
  refine ⟨c₁ + c₂ + c₃, d₁ + d₂ + d₃, ?_⟩
  simpa using
    (calc
      PrefixConditionalComplexity f x ≤
          ((c₁ * logPenalty (BitString.blen x) + d₁) +
            (c₂ * logPenalty (BitString.blen x) + d₂)) +
          (c₃ * logPenalty (BitString.blen x) + d₃) := hk
      _ ≤ (c₁ + c₂ + c₃) * logPenalty (BitString.blen x) + (d₁ + d₂ + d₃) := by
        rw [Nat.add_mul, Nat.add_mul]
        omega)

/-- Lemma 3.3 reduced one step further, to the standard joint-complexity SoI ingredients. -/
theorem lemma33_of_jointRules {f x : Program}
    (hfeature : IsFeature runs f x)
    (hinfo : HighInformationIn f x)
    (hjoint : JointRulesAtFeatureScale f x) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  exact lemma33_of_symmetry hfeature hinfo (symmetricInformationBound_of_jointRules hjoint)

/-- Lemma 3.3 from the current concrete SoI decomposition: a sharp fixed-`x` count bound plus
the two natural scale bounds are enough. -/
theorem lemma33_of_jointRightCountBound {u f x : Program}
    (hu : IsJointRightEnumerator u)
    (hfeature : IsFeature runs f x)
    (hinfo : HighInformationIn f x)
    (hcount : JointRightCountBoundAt (JointComplexity x f) x f)
    (hlowerScale : JointComplexity x f ≤ BitString.blen x)
    (hswapScale : JointComplexity f x ≤ BitString.blen x)
    (hupperScale : PrefixComplexity f + PrefixConditionalComplexity x f ≤ BitString.blen x) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  exact lemma33_of_jointRules hfeature hinfo
    (jointRulesAtFeatureScale_of_jointRightCountBound
      (u := u) (f := f) (x := x) hu hcount hlowerScale hswapScale hupperScale)

/-- Lemma 3.3 from the two concrete enumeration hypotheses: one for the bounded right family and
one for the heavy-left family that supplies the sharp count bound. -/
theorem lemma33_of_jointCountEnumerators {u v f x : Program}
    (hu : IsJointRightEnumerator u)
    (hv : IsJointLeftCountEnumerator v)
    (hfeature : IsFeature runs f x)
    (hinfo : HighInformationIn f x)
    (hlowerScale : JointComplexity x f ≤ BitString.blen x)
    (hswapScale : JointComplexity f x ≤ BitString.blen x)
    (hupperScale : PrefixComplexity f + PrefixConditionalComplexity x f ≤ BitString.blen x) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  exact lemma33_of_jointRules hfeature hinfo
    (jointRulesAtFeatureScale_of_jointCountEnumerators
      (u := u) (v := v) (f := f) (x := x) hu hv hlowerScale hswapScale hupperScale)

end

end Compression

end IcTheory
