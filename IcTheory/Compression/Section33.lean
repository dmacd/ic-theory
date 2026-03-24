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

end

end Compression

end IcTheory
