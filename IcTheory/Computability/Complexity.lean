import IcTheory.Computability.UniversalMachine

namespace IcTheory

namespace UniversalMachine

noncomputable section

/-- Lengths of programs that compute `x` from auxiliary input `r`. -/
def DescriptionLengths (x r : BitString) : Set Nat :=
  {n | ∃ f : Program, BitString.blen f = n ∧ runs f r x}

theorem descriptionLengths_nonempty (x r : BitString) : (DescriptionLengths x r).Nonempty := by
  refine ⟨BitString.blen (codeToProgram (Nat.Partrec.Code.const (BitString.toNatExact x))), ?_⟩
  refine ⟨codeToProgram (Nat.Partrec.Code.const (BitString.toNatExact x)), rfl, ?_⟩
  exact (runs_const_iff (BitString.toNatExact x) r x).2 (BitString.ofNatExact_toNatExact x).symm

/-- The shortest program length computing `x` from `r` on the universal machine. -/
def ConditionalComplexity (x r : BitString) : Nat :=
  sInf (DescriptionLengths x r)

/-- Unconditional description complexity, i.e. with empty auxiliary input. -/
def Complexity (x : BitString) : Nat :=
  ConditionalComplexity x []

/-- `x` is compressible when its shortest description is shorter than the string itself. -/
def Compressible (x : BitString) : Prop :=
  Complexity x < BitString.blen x

/-- `x` is compressible by more than `C` bits. -/
def CompressibleByMoreThan (C : Nat) (x : BitString) : Prop :=
  Complexity x + C < BitString.blen x

theorem conditionalComplexity_mem (x r : BitString) :
    ConditionalComplexity x r ∈ DescriptionLengths x r :=
  Nat.sInf_mem (descriptionLengths_nonempty x r)

theorem exists_program_forConditionalComplexity (x r : BitString) :
    ∃ f : Program, BitString.blen f = ConditionalComplexity x r ∧ runs f r x := by
  exact conditionalComplexity_mem x r

theorem conditionalComplexity_le_length {x r f : BitString} (hf : runs f r x) :
    ConditionalComplexity x r ≤ BitString.blen f := by
  apply Nat.sInf_le
  exact ⟨f, rfl, hf⟩

theorem exists_program_forComplexity (x : BitString) :
    ∃ f : Program, BitString.blen f = Complexity x ∧ runs f [] x := by
  simpa [Complexity] using exists_program_forConditionalComplexity x []

theorem complexity_le_length {x f : BitString} (hf : runs f [] x) :
    Complexity x ≤ BitString.blen f := by
  simpa [Complexity] using conditionalComplexity_le_length hf

end

end UniversalMachine

end IcTheory
