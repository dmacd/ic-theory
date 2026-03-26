import IcTheory.Computability.UniversalMachine

namespace IcTheory

namespace UniversalMachine

open Nat.Partrec

/-- Pair a conditioning input and a residual payload into one machine input. -/
def packedInput (input payload : BitString) : BitString :=
  BitString.ofNatExact (Nat.pair (BitString.toNatExact input) (BitString.toNatExact payload))

@[simp] theorem toNatExact_packedInput (input payload : BitString) :
    BitString.toNatExact (packedInput input payload) =
      Nat.pair (BitString.toNatExact input) (BitString.toNatExact payload) := by
  simp [packedInput]

theorem evalPacked_partrec :
    Nat.Partrec fun n =>
      Code.eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2 := by
  have hfst : Computable₂ (fun a b : ℕ => a) := Computable₂.mk Computable.fst
  have hsnd : Computable₂ (fun a b : ℕ => b) := Computable₂.mk Computable.snd
  have hcode : Computable₂ (fun a b : ℕ => Denumerable.ofNat Code a) :=
    (Computable.ofNat Code).comp₂ hfst
  have hEval : Partrec₂ (fun a b : ℕ => Code.eval (Denumerable.ofNat Code a) b) :=
    Code.eval_part.comp₂ hcode hsnd
  simpa [Nat.unpaired] using (Partrec₂.unpaired'.2 hEval)

theorem exists_applyInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n = Code.eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2 := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalPacked_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- A code that interprets a packed pair `(f, r)` by running `f` on input `r`. -/
noncomputable def applyInterpreterCode : Code :=
  Classical.choose exists_applyInterpreterCode

theorem eval_applyInterpreterCode (n : Nat) :
    Code.eval applyInterpreterCode n =
      Code.eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2 :=
  Classical.choose_spec exists_applyInterpreterCode n

theorem evalOuterApply_partrec :
    Nat.Partrec fun n =>
      Code.eval (Denumerable.ofNat Code n.unpair.2) n.unpair.1 := by
  have hfst : Computable₂ (fun a b : ℕ => a) := Computable₂.mk Computable.fst
  have hsnd : Computable₂ (fun a b : ℕ => b) := Computable₂.mk Computable.snd
  have hcode : Computable₂ (fun a b : ℕ => Denumerable.ofNat Code b) :=
    (Computable.ofNat Code).comp₂ hsnd
  have hEval : Partrec₂ (fun a b : ℕ => Code.eval (Denumerable.ofNat Code b) a) :=
    Code.eval_part.comp₂ hcode hfst
  simpa [Nat.unpaired] using (Partrec₂.unpaired'.2 hEval)

theorem exists_outerApplyInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n = Code.eval (Denumerable.ofNat Code n.unpair.2) n.unpair.1 := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalOuterApply_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/- A code that interprets a packed pair `(input, f)` by running `f` on `input`. -/
noncomputable def outerApplyInterpreterCode : Code :=
  Classical.choose exists_outerApplyInterpreterCode

theorem eval_outerApplyInterpreterCode (n : Nat) :
    Code.eval outerApplyInterpreterCode n =
      Code.eval (Denumerable.ofNat Code n.unpair.2) n.unpair.1 :=
  Classical.choose_spec exists_outerApplyInterpreterCode n

theorem evalEmptyPacked_partrec :
    Nat.Partrec fun n =>
      Code.eval (Denumerable.ofNat Code n.unpair.2) 0 := by
  have hsnd : Computable₂ (fun a b : ℕ => b) := Computable₂.mk Computable.snd
  have hcode : Computable₂ (fun a b : ℕ => Denumerable.ofNat Code b) :=
    (Computable.ofNat Code).comp₂ hsnd
  have hzero : Computable₂ (fun _ _ : ℕ => 0) := Computable₂.mk (Computable.const 0)
  have hEval : Partrec₂ (fun a b : ℕ => Code.eval (Denumerable.ofNat Code b) 0) :=
    Code.eval_part.comp₂ hcode hzero
  simpa [Nat.unpaired] using (Partrec₂.unpaired'.2 hEval)

theorem exists_emptyInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n = Code.eval (Denumerable.ofNat Code n.unpair.2) 0 := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalEmptyPacked_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- A fixed interpreter that ignores the conditioning input and evaluates the payload on empty
input. This gives the basic bridge from plain to prefix complexity. -/
noncomputable def emptyInterpreterCode : Code :=
  Classical.choose exists_emptyInterpreterCode

theorem eval_emptyInterpreterCode (n : Nat) :
    Code.eval emptyInterpreterCode n = Code.eval (Denumerable.ofNat Code n.unpair.2) 0 :=
  Classical.choose_spec exists_emptyInterpreterCode n

/-- Prefix interpreter for ordinary plain descriptions. -/
noncomputable def emptyInterpreter : Program :=
  codeToProgram emptyInterpreterCode

/-- The constant contribution of `emptyInterpreter` inside a prefix program. -/
noncomputable def emptyInterpreterPrefixOverhead : Nat :=
  2 * BitString.blen emptyInterpreter + 2

/-- A fixed interpreter used to witness the prefix-complexity upper bound of Lemma 3.2. -/
noncomputable def applyInterpreter : Program :=
  codeToProgram applyInterpreterCode

/-- Prefix interpreter for plain descriptions relative to the outer conditioning input. -/
noncomputable def outerApplyInterpreter : Program :=
  codeToProgram outerApplyInterpreterCode

/-- The constant contribution of the fixed interpreter inside a prefix program. -/
noncomputable def applyInterpreterPrefixOverhead : Nat :=
  2 * BitString.blen applyInterpreter + 2

/-- The constant contribution of `outerApplyInterpreter` inside a prefix program. -/
noncomputable def outerApplyInterpreterPrefixOverhead : Nat :=
  2 * BitString.blen outerApplyInterpreter + 2

@[simp] theorem runs_applyInterpreter_iff (input payload output : BitString) :
    runs applyInterpreter (packedInput input payload) output ↔ runs input payload output := by
  rw [applyInterpreter, runs_codeToProgram_iff]
  simp [packedInput, runs, programToCode, eval_applyInterpreterCode]

@[simp] theorem runs_outerApplyInterpreter_iff (input payload output : BitString) :
    runs outerApplyInterpreter (packedInput input payload) output ↔ runs payload input output := by
  rw [outerApplyInterpreter, runs_codeToProgram_iff]
  simp [packedInput, runs, programToCode, eval_outerApplyInterpreterCode]

@[simp] theorem runs_emptyInterpreter_iff (input payload output : BitString) :
    runs emptyInterpreter (packedInput input payload) output ↔ runs payload [] output := by
  rw [emptyInterpreter, runs_codeToProgram_iff]
  simp [packedInput, runs, programToCode, eval_emptyInterpreterCode, BitString.toNatExact]

noncomputable section

/-- Prefix-coded execution: a program consists of a fixed interpreter
plus a self-delimiting payload. -/
def PrefixRuns (p input output : BitString) : Prop :=
  ∃ interpreter payload : BitString,
    p = BitString.pair interpreter (BitString.e2 payload) ∧
      runs interpreter (packedInput input payload) output

/-- Prefix description lengths relative to a conditioning input. -/
def PrefixDescriptionLengths (x input : BitString) : Set Nat :=
  {n | ∃ p : Program, BitString.blen p = n ∧ PrefixRuns p input x}

theorem prefixDescriptionLengths_nonempty (x input : BitString) :
    (PrefixDescriptionLengths x input).Nonempty := by
  let interpreter : Program :=
    codeToProgram (Nat.Partrec.Code.const (BitString.toNatExact x))
  let p : Program := BitString.pair interpreter (BitString.e2 [])
  refine ⟨BitString.blen p, p, rfl, ?_⟩
  refine ⟨interpreter, [], rfl, ?_⟩
  exact (runs_const_iff (BitString.toNatExact x) (packedInput input []) x).2
    (BitString.ofNatExact_toNatExact x).symm

/-- Prefix conditional complexity used for the Lemma 3.2 bridge. -/
def PrefixConditionalComplexity (x input : BitString) : Nat :=
  sInf (PrefixDescriptionLengths x input)

/-- Unconditional prefix complexity, i.e. with empty auxiliary input. -/
def PrefixComplexity (x : BitString) : Nat :=
  PrefixConditionalComplexity x []

theorem prefixConditionalComplexity_mem (x input : BitString) :
    PrefixConditionalComplexity x input ∈ PrefixDescriptionLengths x input :=
  Nat.sInf_mem (prefixDescriptionLengths_nonempty x input)

theorem exists_program_forPrefixConditionalComplexity (x input : BitString) :
    ∃ p : Program,
      BitString.blen p = PrefixConditionalComplexity x input ∧
      PrefixRuns p input x := by
  exact prefixConditionalComplexity_mem x input

theorem prefixConditionalComplexity_le_length {x input p : BitString}
    (hp : PrefixRuns p input x) :
    PrefixConditionalComplexity x input ≤ BitString.blen p := by
  apply Nat.sInf_le
  exact ⟨p, rfl, hp⟩

theorem prefixRuns_applyInterpreter_of_runs {f r x : Program} (hf : runs f r x) :
    PrefixRuns (BitString.pair applyInterpreter (BitString.e2 r)) f x := by
  refine ⟨applyInterpreter, r, rfl, ?_⟩
  simpa using (runs_applyInterpreter_iff f r x).2 hf

theorem prefixRuns_outerApplyInterpreter_of_runs {f input x : Program} (hf : runs f input x) :
    PrefixRuns (BitString.pair outerApplyInterpreter (BitString.e2 f)) input x := by
  refine ⟨outerApplyInterpreter, f, rfl, ?_⟩
  simpa using (runs_outerApplyInterpreter_iff input f x).2 hf

theorem prefixRuns_emptyInterpreter_of_runs {f x : Program} (hf : runs f [] x) :
    PrefixRuns (BitString.pair emptyInterpreter (BitString.e2 f)) [] x := by
  refine ⟨emptyInterpreter, f, rfl, ?_⟩
  simpa using (runs_emptyInterpreter_iff ([] : BitString) f x).2 hf

theorem prefixConditionalComplexity_le_applyInterpreter {f r x : Program}
    (hf : runs f r x) :
    PrefixConditionalComplexity x f ≤
      BitString.blen (BitString.pair applyInterpreter (BitString.e2 r)) := by
  exact prefixConditionalComplexity_le_length (prefixRuns_applyInterpreter_of_runs hf)

theorem prefixConditionalComplexity_le_outerApplyInterpreter {f input x : Program}
    (hf : runs f input x) :
    PrefixConditionalComplexity x input ≤
      BitString.blen (BitString.pair outerApplyInterpreter (BitString.e2 f)) := by
  exact prefixConditionalComplexity_le_length (prefixRuns_outerApplyInterpreter_of_runs hf)

theorem prefixComplexity_le_emptyInterpreter {f x : Program}
    (hf : runs f [] x) :
    PrefixComplexity x ≤ BitString.blen (BitString.pair emptyInterpreter (BitString.e2 f)) := by
  simpa [PrefixComplexity] using
    (prefixConditionalComplexity_le_length (prefixRuns_emptyInterpreter_of_runs hf))

end

end UniversalMachine

end IcTheory
