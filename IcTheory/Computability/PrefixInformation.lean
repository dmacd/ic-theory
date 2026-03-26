import IcTheory.Computability.Complexity
import IcTheory.Computability.PrefixComplexity

namespace IcTheory

namespace UniversalMachine

/-- A fixed interpreter that returns the payload part of a packed input. -/
def rightInterpreter : Program :=
  codeToProgram Nat.Partrec.Code.right

/-- The constant contribution of `rightInterpreter` inside a prefix program. -/
def rightInterpreterPrefixOverhead : Nat :=
  2 * BitString.blen rightInterpreter + 2

@[simp] theorem runs_right_packed_iff (input payload output : BitString) :
    runs rightInterpreter (packedInput input payload) output ↔ output = payload := by
  rw [rightInterpreter, runs_codeToProgram_iff]
  constructor
  · intro h
    have h' :
        Part.some (BitString.toNatExact payload) =
          Part.some (BitString.toNatExact output) := by
      simpa [packedInput, Nat.Partrec.Code.eval] using h
    apply BitString.toNatExact_injective
    simpa using h'.symm
  · intro h
    subst output
    simp [packedInput, Nat.Partrec.Code.eval]

theorem prefixRuns_rightPayload (x input : Program) :
    PrefixRuns (BitString.pair rightInterpreter (BitString.e2 x)) input x := by
  refine ⟨rightInterpreter, x, rfl, ?_⟩
  exact (runs_right_packed_iff input x x).2 rfl

theorem prefixConditionalComplexity_le_rightPayload (x input : Program) :
    PrefixConditionalComplexity x input ≤
      BitString.blen x + 2 * BitString.blen (BitString.ofNat (BitString.blen x)) +
        rightInterpreterPrefixOverhead := by
  have h := prefixConditionalComplexity_le_length (prefixRuns_rightPayload x input)
  rw [BitString.blen_pair, BitString.blen_e2] at h
  unfold rightInterpreterPrefixOverhead at *
  omega

theorem prefixConditionalComplexity_log_upper_of_le {x input : Program} {n : Nat}
    (hx : BitString.blen x ≤ n) :
    LogLe (PrefixConditionalComplexity x input) (BitString.blen x) n := by
  refine ⟨2, rightInterpreterPrefixOverhead + 2, ?_⟩
  have hupper := prefixConditionalComplexity_le_rightPayload x input
  have hmono := BitString.blen_ofNat_mono hx
  have hlog := blen_ofNat_le_logPenalty_succ n
  unfold rightInterpreterPrefixOverhead logPenalty at *
  omega

theorem prefixConditionalComplexity_log_upper (x input : Program) :
    LogLe (PrefixConditionalComplexity x input) (BitString.blen x) (BitString.blen x) :=
  prefixConditionalComplexity_log_upper_of_le (x := x) (input := input) le_rfl

theorem prefixConditionalComplexity_le_plainProgramLength {x input f : Program}
    (hf : runs f input x) :
    PrefixConditionalComplexity x input ≤
      BitString.blen f + 2 * BitString.blen (BitString.ofNat (BitString.blen f)) +
        outerApplyInterpreterPrefixOverhead := by
  have h := prefixConditionalComplexity_le_outerApplyInterpreter hf
  rw [BitString.blen_pair, BitString.blen_e2] at h
  unfold outerApplyInterpreterPrefixOverhead at *
  omega

theorem prefixConditionalComplexity_logLe_conditionalComplexity (x input : Program) :
    LogLe (PrefixConditionalComplexity x input)
      (ConditionalComplexity x input)
      (ConditionalComplexity x input) := by
  obtain ⟨f, hfLen, hfRuns⟩ := exists_program_forConditionalComplexity x input
  refine ⟨2, outerApplyInterpreterPrefixOverhead + 2, ?_⟩
  have hupper := prefixConditionalComplexity_le_plainProgramLength hfRuns
  rw [hfLen] at hupper
  have hlog :
      BitString.blen (BitString.ofNat (ConditionalComplexity x input)) ≤
        logPenalty (ConditionalComplexity x input) + 1 := by
    simpa using blen_ofNat_le_logPenalty_succ (ConditionalComplexity x input)
  unfold outerApplyInterpreterPrefixOverhead logPenalty at *
  omega

theorem prefixComplexity_log_upper_of_le {x : Program} {n : Nat}
    (hx : BitString.blen x ≤ n) :
    LogLe (PrefixComplexity x) (BitString.blen x) n := by
  simpa [PrefixComplexity] using
    (prefixConditionalComplexity_log_upper_of_le (x := x) (input := ([] : BitString)) hx)

theorem prefixComplexity_log_upper (x : Program) :
    LogLe (PrefixComplexity x) (BitString.blen x) (BitString.blen x) :=
  prefixComplexity_log_upper_of_le (x := x) le_rfl

theorem prefixComplexity_le_plainProgramLength {x f : Program}
    (hf : runs f [] x) :
    PrefixComplexity x ≤
      BitString.blen f + 2 * BitString.blen (BitString.ofNat (BitString.blen f)) +
        emptyInterpreterPrefixOverhead := by
  have h := prefixComplexity_le_emptyInterpreter hf
  rw [BitString.blen_pair, BitString.blen_e2] at h
  unfold emptyInterpreterPrefixOverhead at *
  omega

/-- Basic bridge from plain to prefix complexity:
a shortest ordinary program gives a prefix program with only logarithmic extra cost. -/
theorem prefixComplexity_logLe_complexity (x : Program) :
    LogLe (PrefixComplexity x) (Complexity x) (Complexity x) := by
  simpa [PrefixComplexity, Complexity] using
    (prefixConditionalComplexity_logLe_conditionalComplexity x ([] : Program))

/-- Paper-facing prefix information `I(f : x) = K(x) - K(x | f)`. -/
noncomputable def PrefixInformation (f x : Program) : Nat :=
  PrefixComplexity x - PrefixConditionalComplexity x f

/-- Joint prefix complexity of two strings, encoded via the exact pairing bridge. -/
noncomputable def JointComplexity (x y : Program) : Nat :=
  PrefixComplexity (packedInput x y)

end UniversalMachine

end IcTheory
