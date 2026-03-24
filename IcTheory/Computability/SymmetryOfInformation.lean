import IcTheory.Computability.PrefixInformation

namespace IcTheory

namespace UniversalMachine

noncomputable section

/-- Upper chain-rule component for joint prefix complexity at scale `n`. -/
def JointUpperChainRuleAt (n : Nat) (x y : Program) : Prop :=
  LogLe (JointComplexity x y)
    (PrefixComplexity x + PrefixConditionalComplexity y x)
    n

/-- Lower chain-rule component for joint prefix complexity at scale `n`. -/
def JointLowerChainRuleAt (n : Nat) (x y : Program) : Prop :=
  LogLe (PrefixComplexity x + PrefixConditionalComplexity y x)
    (JointComplexity x y)
    n

/-- Swap invariance for the chosen joint encoding at scale `n`. -/
def JointSwapInvariantAt (n : Nat) (x y : Program) : Prop :=
  LogEq (JointComplexity x y) (JointComplexity y x) n

/-- Standard SoI consequence from lower chain rule, swap invariance, and upper chain rule. -/
theorem symmetricInformationBound_of_jointRulesAt {n : Nat} {x y : Program}
    (hlower : JointLowerChainRuleAt n x y)
    (hswap : JointSwapInvariantAt n x y)
    (hupper : JointUpperChainRuleAt n y x) :
    LogLe (PrefixComplexity x + PrefixConditionalComplexity y x)
      (PrefixComplexity y + PrefixConditionalComplexity x y)
      n := by
  exact logLe_trans hlower (logLe_trans hswap.1 hupper)

end

end UniversalMachine

end IcTheory
