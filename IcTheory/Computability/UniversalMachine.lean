import IcTheory.Computability.TaggedPrograms

namespace IcTheory

namespace UniversalMachine

open Nat.Partrec

/-- Reserved four-bit sentinel used to mark a stored prefix-replay program. -/
def prefixReplaySentinel : Program := [true, true, true, true]

/-- Plain-program wrapper for replaying a stored prefix description. -/
def prefixReplayPackedProgram (q : Program) : Program :=
  prefixReplaySentinel ++ q

private def prefixReplaySentinelNat : Nat :=
  BitString.toNatExact prefixReplaySentinel

private def prefixReplayHeadNat (p : Program) : Nat :=
  BitString.toNatExact (BitString.splitAt 4 p).1

private def prefixReplayPayloadNat (p : Program) : Nat :=
  BitString.toNatExact (BitString.splitAt 4 p).2

def prefixReplayStoredInterpreterNat (qNat : Nat) : Nat :=
  BitString.toNatExact (decodePrefixDescription (BitString.ofNatExact qNat)).1

def prefixReplayStoredResidualNat (qNat : Nat) : Nat :=
  BitString.toNatExact (decodePrefixDescription (BitString.ofNatExact qNat)).2

private theorem prefixReplayHeadNat_primrec : Primrec prefixReplayHeadNat := by
  unfold prefixReplayHeadNat
  exact BitString.toNatExact_primrec.comp
    (Primrec.fst.comp (BitString.splitAt_primrec.comp (Primrec.const 4) Primrec.id))

private theorem prefixReplayPayloadNat_primrec : Primrec prefixReplayPayloadNat := by
  unfold prefixReplayPayloadNat
  exact BitString.toNatExact_primrec.comp
    (Primrec.snd.comp (BitString.splitAt_primrec.comp (Primrec.const 4) Primrec.id))

private theorem prefixReplayStoredInterpreterNat_computable :
    Computable prefixReplayStoredInterpreterNat := by
  unfold prefixReplayStoredInterpreterNat
  exact BitString.toNatExact_computable.comp
    (Computable.fst.comp
      (decodePrefixDescription_computable.comp BitString.ofNatExact_computable))

private theorem prefixReplayStoredResidualNat_computable :
    Computable prefixReplayStoredResidualNat := by
  unfold prefixReplayStoredResidualNat
  exact BitString.toNatExact_computable.comp
    (Computable.snd.comp
      (decodePrefixDescription_computable.comp BitString.ofNatExact_computable))

private theorem evalPrefixReplay_partrec :
    Nat.Partrec fun n =>
      Code.eval
        (decodeAdditiveProgramNat (prefixReplayStoredInterpreterNat n.unpair.1))
        (Nat.pair n.unpair.2 (prefixReplayStoredResidualNat n.unpair.1)) := by
  have hQNat : Computable fun n : Nat => n.unpair.1 := by
    exact Computable.fst.comp Computable.unpair
  have hInputNat : Computable fun n : Nat => n.unpair.2 := by
    exact Computable.snd.comp Computable.unpair
  have hCode : Computable fun n : Nat =>
      decodeAdditiveProgramNat (prefixReplayStoredInterpreterNat n.unpair.1) := by
    exact decodeAdditiveProgramNat_computable.comp
      (prefixReplayStoredInterpreterNat_computable.comp hQNat)
  have hPacked : Computable fun n : Nat =>
      Nat.pair n.unpair.2 (prefixReplayStoredResidualNat n.unpair.1) := by
    exact (Primrec₂.natPair.to_comp).comp
      hInputNat
      (prefixReplayStoredResidualNat_computable.comp hQNat)
  exact Partrec.nat_iff.1 (Code.eval_part.comp hCode hPacked)

theorem exists_prefixReplayInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n =
        Code.eval
          (decodeAdditiveProgramNat (prefixReplayStoredInterpreterNat n.unpair.1))
          (Nat.pair n.unpair.2 (prefixReplayStoredResidualNat n.unpair.1)) := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalPrefixReplay_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- Fixed code used to replay a stored prefix description under ordinary plain execution. -/
noncomputable def prefixReplayInterpreterCode : Code :=
  Classical.choose exists_prefixReplayInterpreterCode

theorem eval_prefixReplayInterpreterCode (n : Nat) :
    Code.eval prefixReplayInterpreterCode n =
      Code.eval
        (decodeAdditiveProgramNat (prefixReplayStoredInterpreterNat n.unpair.1))
        (Nat.pair n.unpair.2 (prefixReplayStoredResidualNat n.unpair.1)) :=
  Classical.choose_spec exists_prefixReplayInterpreterCode n

/-- Interpret an exact bitstring as a partial-recursive program code. -/
noncomputable def programToCode (p : Program) : Code :=
  if prefixReplayHeadNat p = prefixReplaySentinelNat then
    Code.curry prefixReplayInterpreterCode (prefixReplayPayloadNat p)
  else
    additiveProgramToCode p

/-- Reify a `Nat.Partrec.Code` back into a bitstring program. -/
def codeToProgram (c : Code) : Program :=
  additiveCodeToProgram c

@[simp] theorem programToCode_codeToProgram (c : Code) :
    programToCode (codeToProgram c) = c := by
  have hneq :
      prefixReplayHeadNat (additiveCodeToProgram c) ≠ prefixReplaySentinelNat := by
    intro h
    cases c <;> simp [prefixReplayHeadNat, prefixReplaySentinelNat, prefixReplaySentinel,
      additiveCodeToProgram, BitString.splitAt_eq_take_drop, BitString.toNatExact] at h <;> cases h
  simp [programToCode, codeToProgram, hneq]

theorem programToCode_primrec : Primrec programToCode := by
  refine Primrec.ite ?_ ?_ ?_
  · exact Primrec.eq.comp prefixReplayHeadNat_primrec (Primrec.const prefixReplaySentinelNat)
  · exact Nat.Partrec.Code.primrec₂_curry.comp
      (Primrec.const prefixReplayInterpreterCode)
      prefixReplayPayloadNat_primrec
  · simpa [additiveProgramToCode] using
      (decodeAdditiveProgramNat_primrec.comp BitString.toNatExact_primrec)

theorem programToCode_computable : Computable programToCode :=
  programToCode_primrec.to_comp

/-- Interpret a stored natural payload using the active plain-program semantics. -/
noncomputable def storedProgramCode (n : Nat) : Code :=
  programToCode (BitString.ofNatExact n)

@[simp] theorem storedProgramCode_toNatExact (p : Program) :
    storedProgramCode (BitString.toNatExact p) = programToCode p := by
  simp [storedProgramCode]

theorem storedProgramCode_computable : Computable storedProgramCode := by
  unfold storedProgramCode
  exact programToCode_computable.comp BitString.ofNatExact_computable

/-- The concrete execution relation induced by `Nat.Partrec.Code.eval`. -/
def runs : Runs := fun p input output =>
  Code.eval (programToCode p) (BitString.toNatExact input) = Part.some (BitString.toNatExact output)

theorem runs_iff (p input output : BitString) :
    runs p input output ↔
      Code.eval (programToCode p) (BitString.toNatExact input) =
        Part.some (BitString.toNatExact output) := by
  rfl

@[simp] theorem programToCode_prefixReplayPackedProgram (q : Program) :
    programToCode (prefixReplayPackedProgram q) =
      Code.curry prefixReplayInterpreterCode (BitString.toNatExact q) := by
  simp [programToCode, prefixReplayPackedProgram, prefixReplaySentinel,
    prefixReplayHeadNat, prefixReplayPayloadNat, prefixReplaySentinelNat,
    BitString.splitAt_eq_take_drop]

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
    Nat.Partrec fun n => Code.eval (programToCode (BitString.ofNatExact n)) 0 := by
  exact Partrec.nat_iff.1
    (Code.eval_part.comp
      (programToCode_computable.comp BitString.ofNatExact_computable)
      (Computable.const (α := ℕ) 0))

theorem exists_universalFeatureCode :
    ∃ c : Code, ∀ n : Nat, Code.eval c n = Code.eval (programToCode (BitString.ofNatExact n)) 0 := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalOnEmpty_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

noncomputable def universalFeatureCode : Code :=
  Classical.choose exists_universalFeatureCode

theorem eval_universalFeatureCode (n : Nat) :
    Code.eval universalFeatureCode n = Code.eval (programToCode (BitString.ofNatExact n)) 0 :=
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
