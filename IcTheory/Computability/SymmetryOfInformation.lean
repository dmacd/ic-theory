import IcTheory.Computability.PrefixInformation

namespace IcTheory

namespace UniversalMachine

open Nat.Partrec

noncomputable section

/-- Payload format for the missing joint upper-chain interpreter.
It stores the residual/interpreter pieces of two prefix descriptions in a machine-readable exact
code. -/
def JointUpperPayload (s f r g : Program) : Program :=
  BitString.exactQuadPayload s f r g

@[simp] theorem decode_jointUpperPayload (s f r g : Program) :
    BitString.decodeExactQuadPayload (JointUpperPayload s f r g) = (s, f, r, g) := by
  simp [JointUpperPayload]

/-- Specification of a fixed interpreter witnessing the upper chain rule:
it reconstructs `x` from `(f, s)`, then `y` from `(g, r)`, and outputs the joint encoding. -/
def IsJointUpperInterpreter (u : Program) : Prop :=
  ∀ f s g r x y : Program,
    runs f (packedInput [] s) x →
      runs g (packedInput x r) y →
        runs u (packedInput [] (JointUpperPayload s f r g)) (packedInput x y)

private def jointUpperDecoded (n : Nat) : Program × Program × Program × Program :=
  BitString.decodeExactQuadPayload (BitString.ofNatExact n.unpair.2)

private theorem jointUpperDecoded_computable : Computable jointUpperDecoded := by
  exact BitString.decodeExactQuadPayload_computable.comp
    (BitString.ofNatExact_computable.comp (Computable.snd.comp Computable.unpair))

private def jointUpperResidualNat (n : Nat) : Nat :=
  BitString.toNatExact (jointUpperDecoded n).1

private def jointUpperFirstCodeNat (n : Nat) : Nat :=
  BitString.toNatExact (jointUpperDecoded n).2.1

private def jointUpperSecondResidualNat (n : Nat) : Nat :=
  BitString.toNatExact (jointUpperDecoded n).2.2.1

private def jointUpperSecondCodeNat (n : Nat) : Nat :=
  BitString.toNatExact (jointUpperDecoded n).2.2.2

private theorem jointUpperResidualNat_computable : Computable jointUpperResidualNat := by
  exact BitString.toNatExact_computable.comp (Computable.fst.comp jointUpperDecoded_computable)

private theorem jointUpperFirstCodeNat_computable : Computable jointUpperFirstCodeNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.fst.comp (Computable.snd.comp jointUpperDecoded_computable))

private theorem jointUpperSecondResidualNat_computable :
    Computable jointUpperSecondResidualNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.fst.comp
      (Computable.snd.comp (Computable.snd.comp jointUpperDecoded_computable)))

private theorem jointUpperSecondCodeNat_computable : Computable jointUpperSecondCodeNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp jointUpperDecoded_computable)))

private theorem evalJointUpper_partrec :
    Nat.Partrec fun n =>
      Code.eval (Denumerable.ofNat Code (jointUpperFirstCodeNat n))
          (Nat.pair 0 (jointUpperResidualNat n)) >>= fun xNat =>
        Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
            (Nat.pair xNat (jointUpperSecondResidualNat n)) >>= fun yNat =>
          Part.some (Nat.pair xNat yNat) := by
  have hFirstCode : Computable fun n => Denumerable.ofNat Code (jointUpperFirstCodeNat n) := by
    exact (Computable.ofNat Code).comp jointUpperFirstCodeNat_computable
  have hFirstInput : Computable fun n => Nat.pair 0 (jointUpperResidualNat n) := by
    exact (Primrec₂.natPair.to_comp).comp (Computable.const 0) jointUpperResidualNat_computable
  have hEval₁ : _root_.Partrec fun n =>
      Code.eval (Denumerable.ofNat Code (jointUpperFirstCodeNat n))
        (Nat.pair 0 (jointUpperResidualNat n)) := by
    exact Code.eval_part.comp hFirstCode hFirstInput
  have hSecondCode : Computable fun p : Nat × Nat =>
      Denumerable.ofNat Code (jointUpperSecondCodeNat p.1) := by
    exact (Computable.ofNat Code).comp (jointUpperSecondCodeNat_computable.comp Computable.fst)
  have hSecondInput : Computable fun p : Nat × Nat =>
      Nat.pair p.2 (jointUpperSecondResidualNat p.1) := by
    exact (Primrec₂.natPair.to_comp).comp Computable.snd
      (jointUpperSecondResidualNat_computable.comp Computable.fst)
  have hEval₂ : _root_.Partrec fun p : Nat × Nat =>
      Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat p.1))
        (Nat.pair p.2 (jointUpperSecondResidualNat p.1)) := by
    exact Code.eval_part.comp hSecondCode hSecondInput
  have hPack : _root_.Partrec₂ fun n xNat =>
      Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
          (Nat.pair xNat (jointUpperSecondResidualNat n)) >>= fun yNat =>
        Part.some (Nat.pair xNat yNat) := by
    have hOut : Computable₂ fun (p : Nat × Nat) (yNat : Nat) => Nat.pair p.2 yNat := by
      exact (Primrec₂.natPair.to_comp).comp (Computable.snd.comp Computable.fst) Computable.snd
    simpa using (hEval₂.bind hOut.partrec₂).to₂
  exact _root_.Partrec.nat_iff.1 (hEval₁.bind hPack)

theorem exists_jointUpperInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n =
        Code.eval (Denumerable.ofNat Code (jointUpperFirstCodeNat n))
            (Nat.pair 0 (jointUpperResidualNat n)) >>= fun xNat =>
          Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
              (Nat.pair xNat (jointUpperSecondResidualNat n)) >>= fun yNat =>
            Part.some (Nat.pair xNat yNat) := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalJointUpper_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- A fixed program that decodes `JointUpperPayload`, executes the two stored descriptions in
sequence, and returns the packed output. -/
noncomputable def jointUpperInterpreterCode : Code :=
  Classical.choose exists_jointUpperInterpreterCode

theorem eval_jointUpperInterpreterCode (n : Nat) :
    Code.eval jointUpperInterpreterCode n =
      Code.eval (Denumerable.ofNat Code (jointUpperFirstCodeNat n))
          (Nat.pair 0 (jointUpperResidualNat n)) >>= fun xNat =>
        Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
            (Nat.pair xNat (jointUpperSecondResidualNat n)) >>= fun yNat =>
          Part.some (Nat.pair xNat yNat) :=
  Classical.choose_spec exists_jointUpperInterpreterCode n

/-- Concrete interpreter witnessing the joint upper-chain rule. -/
noncomputable def jointUpperInterpreter : Program :=
  codeToProgram jointUpperInterpreterCode

theorem jointUpperInterpreter_isJointUpperInterpreter :
    IsJointUpperInterpreter jointUpperInterpreter := by
  intro f s g r x y hf hg
  have hf' :
      Code.eval (Denumerable.ofNat Code (BitString.toNatExact f))
          (Nat.pair 0 (BitString.toNatExact s)) =
        Part.some (BitString.toNatExact x) := by
    simpa [runs, programToCode, toNatExact_packedInput] using hf
  have hg' :
      Code.eval (Denumerable.ofNat Code (BitString.toNatExact g))
          (Nat.pair (BitString.toNatExact x) (BitString.toNatExact r)) =
        Part.some (BitString.toNatExact y) := by
    simpa [runs, programToCode, toNatExact_packedInput] using hg
  rw [jointUpperInterpreter, runs_codeToProgram_iff, toNatExact_packedInput]
  simp [eval_jointUpperInterpreterCode, jointUpperFirstCodeNat, jointUpperResidualNat,
    jointUpperSecondCodeNat, jointUpperSecondResidualNat, jointUpperDecoded, JointUpperPayload,
    toNatExact_packedInput, hf', hg']

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

/-- Constant contribution of a fixed upper-chain interpreter inside the composed prefix witness. -/
def jointUpperInterpreterPrefixOverhead (u : Program) : Nat :=
  2 * BitString.blen u + 11

/-- A fixed interpreter satisfying `IsJointUpperInterpreter` yields the standard joint upper
chain rule at the natural scale `K(x) + K(y | x)`. -/
theorem jointUpperChainRuleAt_complexityScale_of_interpreter {u x y : Program}
    (hu : IsJointUpperInterpreter u) :
    JointUpperChainRuleAt (PrefixComplexity x + PrefixConditionalComplexity y x) x y := by
  obtain ⟨p₁, hp₁Len, hp₁Runs⟩ := exists_program_forPrefixConditionalComplexity x []
  rcases hp₁Runs with ⟨f, s, hp₁Eq, hf⟩
  obtain ⟨p₂, hp₂Len, hp₂Runs⟩ := exists_program_forPrefixConditionalComplexity y x
  rcases hp₂Runs with ⟨g, r, hp₂Eq, hg⟩
  let payload : Program := JointUpperPayload s f r g
  let p : Program := BitString.pair u (BitString.e2 payload)
  have hpRuns : PrefixRuns p [] (packedInput x y) := by
    refine ⟨u, payload, rfl, ?_⟩
    exact hu f s g r x y hf hg
  have hjoint : JointComplexity x y ≤ BitString.blen p := by
    simpa [JointComplexity, PrefixComplexity] using prefixConditionalComplexity_le_length hpRuns
  have hpayload :
      BitString.blen payload ≤
        PrefixComplexity x + PrefixConditionalComplexity y x +
          (2 * BitString.blen (BitString.ofNat (PrefixComplexity x)) + 1) := by
    have h := BitString.blen_exactQuadPayload_le_twoPrefixPrograms s f r g
    rw [← hp₁Eq, ← hp₂Eq, hp₁Len, hp₂Len] at h
    simpa [payload, JointUpperPayload, PrefixComplexity] using h
  have hx :
      PrefixComplexity x ≤ PrefixComplexity x + PrefixConditionalComplexity y x := by
    exact Nat.le_add_right _ _
  have hlogx :
      BitString.blen (BitString.ofNat (PrefixComplexity x)) ≤
        logPenalty (PrefixComplexity x + PrefixConditionalComplexity y x) + 1 := by
    have hsize := blen_ofNat_le_logPenalty_succ (PrefixComplexity x)
    have hmono := logPenalty_mono hx
    omega
  have hpayloadScale :
      BitString.blen payload ≤
        4 * (PrefixComplexity x + PrefixConditionalComplexity y x) + 1 := by
    have hsize := BitString.blen_ofNat_le_self (PrefixComplexity x)
    omega
  have hlogPayload :
      BitString.blen (BitString.ofNat (BitString.blen payload)) ≤
        logPenalty (PrefixComplexity x + PrefixConditionalComplexity y x) + 3 := by
    exact blen_ofNat_le_logPenalty_add_three_of_le_four_mul_add_three
      (by omega : BitString.blen payload ≤
        4 * (PrefixComplexity x + PrefixConditionalComplexity y x) + 3)
  have hjoint' :
      JointComplexity x y ≤
        1 + (1 + (2 * BitString.blen u +
          (BitString.blen payload +
            2 * BitString.blen (BitString.ofNat (BitString.blen payload))))) := by
    simpa [p, BitString.blen_pair, BitString.blen_e2, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hjoint
  refine ⟨4, jointUpperInterpreterPrefixOverhead u, ?_⟩
  unfold jointUpperInterpreterPrefixOverhead
  omega

/-- The same upper-chain theorem, rescaled along any larger comparison parameter. -/
theorem jointUpperChainRuleAt_of_interpreter_of_scale_le {u x y : Program} {n : Nat}
    (hu : IsJointUpperInterpreter u)
    (hscale : PrefixComplexity x + PrefixConditionalComplexity y x ≤ n) :
    JointUpperChainRuleAt n x y := by
  exact logLe_of_scale_le (jointUpperChainRuleAt_complexityScale_of_interpreter hu) hscale

end

end UniversalMachine

end IcTheory
