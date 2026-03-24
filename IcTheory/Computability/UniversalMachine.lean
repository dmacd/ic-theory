import IcTheory.Compression.Feature
import Mathlib.Computability.PartrecCode

namespace IcTheory

namespace UniversalMachine

open Nat.Partrec

/-- Interpret an exact bitstring as a partial-recursive program code. -/
def programToCode (p : Program) : Code :=
  Denumerable.ofNat Code (BitString.toNatExact p)

/-- Reify a `Nat.Partrec.Code` back into a bitstring program. -/
def codeToProgram (c : Code) : Program :=
  BitString.ofNatExact (Encodable.encode c)

@[simp] theorem programToCode_codeToProgram (c : Code) :
    programToCode (codeToProgram c) = c := by
  simp [programToCode, codeToProgram]

@[simp] theorem codeToProgram_programToCode (p : Program) :
    codeToProgram (programToCode p) = p := by
  simp [programToCode, codeToProgram]

/-- The concrete execution relation induced by `Nat.Partrec.Code.eval`. -/
def runs : Runs := fun p input output =>
  Code.eval (programToCode p) (BitString.toNatExact input) = Part.some (BitString.toNatExact output)

theorem runs_iff (p input output : BitString) :
    runs p input output ↔
      Code.eval (programToCode p) (BitString.toNatExact input) =
        Part.some (BitString.toNatExact output) := by
  rfl

@[simp] theorem runs_codeToProgram_iff (c : Code) (input output : BitString) :
    runs (codeToProgram c) input output ↔
      Code.eval c (BitString.toNatExact input) = Part.some (BitString.toNatExact output) := by
  simp [runs]

@[simp] theorem runs_zero_iff (input output : BitString) :
    runs (codeToProgram Code.zero) input output ↔ output = [] := by
  rw [runs_codeToProgram_iff]
  constructor
  · intro h
    have h0 : Code.eval Code.zero (BitString.toNatExact input) = Part.some 0 := rfl
    rw [h0] at h
    apply BitString.toNatExact_injective
    simpa using h.symm
  · intro h
    subst output
    rfl

@[simp] theorem runs_id_iff (input output : BitString) :
    runs (codeToProgram Code.id) input output ↔ output = input := by
  rw [runs_codeToProgram_iff]
  constructor
  · intro h
    have h' : Part.some (BitString.toNatExact input) = Part.some (BitString.toNatExact output) := by
      simpa using h
    apply BitString.toNatExact_injective
    simpa using h'.symm
  · intro h
    subst output
    exact Nat.Partrec.Code.eval_id (BitString.toNatExact input)

@[simp] theorem runs_const_iff (n : Nat) (input output : BitString) :
    runs (codeToProgram (Code.const n)) input output ↔ output = BitString.ofNatExact n := by
  rw [runs_codeToProgram_iff]
  constructor
  · intro h
    have h' : Part.some n = Part.some (BitString.toNatExact output) := by
      simpa using h
    apply BitString.toNatExact_injective
    simpa using h'.symm
  · intro h
    subst output
    simp [Nat.Partrec.Code.eval_const]

theorem evalOnEmpty_partrec :
    Nat.Partrec fun n => Code.eval (Denumerable.ofNat Code n) 0 := by
  exact Partrec.nat_iff.1
    (Code.eval_part.comp (Computable.ofNat Code) (Computable.const (α := ℕ) 0))

theorem exists_universalFeatureCode :
    ∃ c : Code, ∀ n : Nat, Code.eval c n = Code.eval (Denumerable.ofNat Code n) 0 := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalOnEmpty_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

noncomputable def universalFeatureCode : Code :=
  Classical.choose exists_universalFeatureCode

theorem eval_universalFeatureCode (n : Nat) :
    Code.eval universalFeatureCode n = Code.eval (Denumerable.ofNat Code n) 0 :=
  Classical.choose_spec exists_universalFeatureCode n

/-- A fixed universal feature program that evaluates the residual on empty input. -/
noncomputable def universalFeature : Program :=
  codeToProgram universalFeatureCode

/-- The description-length overhead contributed by `universalFeature`. -/
noncomputable def universalFeatureConstant : Nat :=
  BitString.blen universalFeature

@[simp] theorem runs_universalFeature_iff (r x : BitString) :
    runs universalFeature r x ↔ runs r [] x := by
  rw [universalFeature, runs_codeToProgram_iff, runs_iff]
  simp [programToCode, eval_universalFeatureCode, BitString.toNatExact]

end UniversalMachine

end IcTheory
