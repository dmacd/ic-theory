import IcTheory.Computability.TaggedPrograms

namespace IcTheory

namespace UniversalMachine

open Nat.Partrec

/-- Reserved four-bit sentinel used to mark a stored prefix-replay program. -/
def prefixReplaySentinel : Program := [true, true, true, true]

/-- Plain-program wrapper for replaying a stored prefix description. -/
def prefixReplayPackedProgram (q : Program) : Program :=
  prefixReplaySentinel ++ q

/-- Reserved four-bit sentinel used to mark a stored postcomposition pair `(g, p)`. -/
def postcomposeSentinel : Program := [false, true, true, true]

/-- Plain-program wrapper for composing two stored plain programs. -/
def postcomposePackedProgram (g p : Program) : Program :=
  postcomposeSentinel ++ BitString.exactPairPayload g p

/-- Reserved four-bit sentinel used to mark a stored raw payload. -/
def storedValueSentinel : Program := [false, false, false, true]

/-- Plain-program wrapper for replaying a stored raw payload directly as output. -/
def storedValuePackedProgram (p : Program) : Program :=
  storedValueSentinel ++ p

private def prefixReplaySentinelNat : Nat :=
  BitString.toNatExact prefixReplaySentinel

private def postcomposeSentinelNat : Nat :=
  BitString.toNatExact postcomposeSentinel

private def storedValueSentinelNat : Nat :=
  BitString.toNatExact storedValueSentinel

private def outerHeadNat (p : Program) : Nat :=
  BitString.toNatExact (BitString.splitAt 4 p).1

private def outerPayloadProgram (p : Program) : Program :=
  (BitString.splitAt 4 p).2

private def outerPayloadNat (p : Program) : Nat :=
  BitString.toNatExact (outerPayloadProgram p)

def prefixReplayStoredInterpreterNat (qNat : Nat) : Nat :=
  BitString.toNatExact (decodePrefixDescription (BitString.ofNatExact qNat)).1

def prefixReplayStoredResidualNat (qNat : Nat) : Nat :=
  BitString.toNatExact (decodePrefixDescription (BitString.ofNatExact qNat)).2

private theorem outerHeadNat_primrec : Primrec outerHeadNat := by
  unfold outerHeadNat
  exact BitString.toNatExact_primrec.comp
    (Primrec.fst.comp (BitString.splitAt_primrec.comp (Primrec.const 4) Primrec.id))

private theorem outerPayloadProgram_primrec : Primrec outerPayloadProgram := by
  unfold outerPayloadProgram
  exact Primrec.snd.comp (BitString.splitAt_primrec.comp (Primrec.const 4) Primrec.id)

private theorem outerPayloadNat_primrec : Primrec outerPayloadNat := by
  unfold outerPayloadNat
  exact BitString.toNatExact_primrec.comp outerPayloadProgram_primrec

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

private def postcomposeDecoded (p : Program) : Program × Program :=
  BitString.decodeExactPairPayload (outerPayloadProgram p)

private theorem postcomposeDecoded_primrec : Primrec postcomposeDecoded := by
  unfold postcomposeDecoded
  exact BitString.decodeExactPairPayload_primrec.comp outerPayloadProgram_primrec

private theorem additiveProgramToCode_primrec : Primrec additiveProgramToCode := by
  simpa [additiveProgramToCode] using
    (decodeAdditiveProgramNat_primrec.comp BitString.toNatExact_primrec)

private def twoCodeCompOrZero (cs : List Code) : Code :=
  bif cs.length == 2 then
    Code.comp ((cs[0]?).getD Code.zero) ((cs[1]?).getD Code.zero)
  else
    Code.zero

@[simp] private theorem twoCodeCompOrZero_pair (cg cp : Code) :
    twoCodeCompOrZero [cg, cp] = Code.comp cg cp := by
  simp [twoCodeCompOrZero]

private theorem twoCodeCompOrZero_primrec : Primrec twoCodeCompOrZero := by
  unfold twoCodeCompOrZero
  have hlen : Primrec fun cs : List Code => cs.length := Primrec.list_length
  have hfirst :
      Primrec fun cs : List Code => (cs[0]?).getD Code.zero := by
    exact Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0))
      (Primrec.const Code.zero)
  have hsecond :
      Primrec fun cs : List Code => (cs[1]?).getD Code.zero := by
    exact Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.id (Primrec.const 1))
      (Primrec.const Code.zero)
  have hcomp :
      Primrec fun cs : List Code => Code.comp ((cs[0]?).getD Code.zero) ((cs[1]?).getD Code.zero) := by
    exact Nat.Partrec.Code.primrec₂_comp.comp hfirst hsecond
  simpa using
    (Primrec.cond
      (Primrec.beq.comp hlen (Primrec.const 2))
      hcomp
      (Primrec.const Code.zero))

private def programToCodeChildren : Program → List Program
  | false :: true :: true :: true :: payload =>
      let gp := BitString.decodeExactPairPayload payload
      [gp.1, gp.2]
  | _ => []

private theorem programToCodeChildren_eq_headBased (p : Program) :
    programToCodeChildren p =
      if outerHeadNat p = postcomposeSentinelNat then
        let gp := postcomposeDecoded p
        [gp.1, gp.2]
      else
        [] := by
  cases p with
  | nil =>
      simp [programToCodeChildren, outerHeadNat, outerPayloadProgram, postcomposeDecoded,
        postcomposeSentinel, postcomposeSentinelNat, BitString.splitAt_eq_take_drop,
        BitString.toNatExact]
  | cons b₁ t₁ =>
      cases t₁ with
      | nil =>
          cases b₁ <;>
            simp [programToCodeChildren, outerHeadNat, outerPayloadProgram, postcomposeDecoded,
              postcomposeSentinel, postcomposeSentinelNat, BitString.splitAt_eq_take_drop,
              BitString.toNatExact]
      | cons b₂ t₂ =>
          cases t₂ with
          | nil =>
              cases b₁ <;> cases b₂ <;>
                simp [programToCodeChildren, outerHeadNat, outerPayloadProgram, postcomposeDecoded,
                  postcomposeSentinel, postcomposeSentinelNat, BitString.splitAt_eq_take_drop,
                  BitString.toNatExact]
          | cons b₃ t₃ =>
              cases t₃ with
              | nil =>
                  cases b₁ <;> cases b₂ <;> cases b₃ <;>
                    simp [programToCodeChildren, outerHeadNat, outerPayloadProgram,
                      postcomposeDecoded, postcomposeSentinel, postcomposeSentinelNat,
                      BitString.splitAt_eq_take_drop, BitString.toNatExact]
              | cons b₄ payload =>
                  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
                    simp [programToCodeChildren, outerHeadNat, outerPayloadProgram,
                      postcomposeDecoded, postcomposeSentinel, postcomposeSentinelNat,
                      BitString.splitAt_eq_take_drop, BitString.toNatExact]

private theorem programToCodeChildren_primrec : Primrec programToCodeChildren := by
  rw [show programToCodeChildren =
    (fun p =>
      if outerHeadNat p = postcomposeSentinelNat then
        let gp := postcomposeDecoded p
        [gp.1, gp.2]
      else
        []) from funext programToCodeChildren_eq_headBased]
  refine Primrec.ite ?_ ?_ ?_
  · exact Primrec.eq.comp outerHeadNat_primrec (Primrec.const postcomposeSentinelNat)
  · exact (Primrec.list_cons.comp
      (Primrec.fst.comp postcomposeDecoded_primrec)
      (Primrec.list_cons.comp
        (Primrec.snd.comp postcomposeDecoded_primrec)
        (Primrec.const ([] : List Program))))
  · exact Primrec.const ([] : List Program)

private noncomputable def programToCodeStep : Program → List Code → Option Code
  | true :: true :: true :: true :: q, _ =>
      some (Code.curry prefixReplayInterpreterCode (BitString.toNatExact q))
  | false :: true :: true :: true :: _, cs =>
      some (twoCodeCompOrZero cs)
  | false :: false :: false :: true :: payload, _ =>
      some (Code.curry Code.left (BitString.toNatExact payload))
  | p, _ =>
      some (additiveProgramToCode p)

private theorem programToCodeStep_eq_headBased (p : Program) (cs : List Code) :
    programToCodeStep p cs =
      if outerHeadNat p = prefixReplaySentinelNat then
        some (Code.curry prefixReplayInterpreterCode (outerPayloadNat p))
      else if outerHeadNat p = postcomposeSentinelNat then
        some (twoCodeCompOrZero cs)
      else if outerHeadNat p = storedValueSentinelNat then
        some (Code.curry Code.left (outerPayloadNat p))
      else
        some (additiveProgramToCode p) := by
  cases p with
  | nil =>
      simp [programToCodeStep, outerHeadNat, outerPayloadNat, outerPayloadProgram,
        prefixReplaySentinel, prefixReplaySentinelNat, postcomposeSentinel,
        postcomposeSentinelNat, storedValueSentinel, storedValueSentinelNat,
        BitString.splitAt_eq_take_drop, BitString.toNatExact]
  | cons b₁ t₁ =>
      cases t₁ with
      | nil =>
          cases b₁ <;>
            simp [programToCodeStep, outerHeadNat, outerPayloadNat, outerPayloadProgram,
              prefixReplaySentinel, prefixReplaySentinelNat, postcomposeSentinel,
              postcomposeSentinelNat, storedValueSentinel, storedValueSentinelNat,
              BitString.splitAt_eq_take_drop, BitString.toNatExact]
      | cons b₂ t₂ =>
          cases t₂ with
          | nil =>
              cases b₁ <;> cases b₂ <;>
                simp [programToCodeStep, outerHeadNat, outerPayloadNat, outerPayloadProgram,
                  prefixReplaySentinel, prefixReplaySentinelNat, postcomposeSentinel,
                  postcomposeSentinelNat, storedValueSentinel, storedValueSentinelNat,
                  BitString.splitAt_eq_take_drop, BitString.toNatExact]
          | cons b₃ t₃ =>
              cases t₃ with
              | nil =>
                  cases b₁ <;> cases b₂ <;> cases b₃ <;>
                    simp [programToCodeStep, outerHeadNat, outerPayloadNat, outerPayloadProgram,
                      prefixReplaySentinel, prefixReplaySentinelNat, postcomposeSentinel,
                      postcomposeSentinelNat, storedValueSentinel, storedValueSentinelNat,
                      BitString.splitAt_eq_take_drop, BitString.toNatExact]
              | cons b₄ payload =>
                  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
                    simp [programToCodeStep, outerHeadNat, outerPayloadNat, outerPayloadProgram,
                      prefixReplaySentinel, prefixReplaySentinelNat, postcomposeSentinel,
                      postcomposeSentinelNat, storedValueSentinel, storedValueSentinelNat,
                      BitString.splitAt_eq_take_drop, BitString.toNatExact]

private theorem programToCodeStep_primrec : Primrec₂ programToCodeStep := by
  rw [show programToCodeStep =
    (fun p cs =>
      if outerHeadNat p = prefixReplaySentinelNat then
        some (Code.curry prefixReplayInterpreterCode (outerPayloadNat p))
      else if outerHeadNat p = postcomposeSentinelNat then
        some (twoCodeCompOrZero cs)
      else if outerHeadNat p = storedValueSentinelNat then
        some (Code.curry Code.left (outerPayloadNat p))
      else
        some (additiveProgramToCode p)) from funext (fun p => funext (programToCodeStep_eq_headBased p))]
  refine Primrec.ite ?_ ?_ ?_
  · exact (Primrec.eq.comp (outerHeadNat_primrec.comp Primrec.fst)
      (Primrec.const prefixReplaySentinelNat))
  · exact (Primrec.option_some.comp
      (Nat.Partrec.Code.primrec₂_curry.comp
        (Primrec.const prefixReplayInterpreterCode)
        (outerPayloadNat_primrec.comp Primrec.fst))).to₂
  · refine Primrec.ite ?_ ?_ ?_
    · exact (Primrec.eq.comp (outerHeadNat_primrec.comp Primrec.fst)
        (Primrec.const postcomposeSentinelNat))
    · exact (Primrec.option_some.comp (twoCodeCompOrZero_primrec.comp Primrec.snd)).to₂
    · refine Primrec.ite ?_ ?_ ?_
      · exact (Primrec.eq.comp (outerHeadNat_primrec.comp Primrec.fst)
          (Primrec.const storedValueSentinelNat))
      · exact (Primrec.option_some.comp
          (Nat.Partrec.Code.primrec₂_curry.comp
            (Primrec.const Code.left)
            (outerPayloadNat_primrec.comp Primrec.fst))).to₂
      · exact (Primrec.option_some.comp (additiveProgramToCode_primrec.comp Primrec.fst)).to₂

/-- Interpret an exact bitstring as a partial-recursive program code. -/
noncomputable def programToCode : Program → Code
  | true :: true :: true :: true :: q =>
      Code.curry prefixReplayInterpreterCode (BitString.toNatExact q)
  | false :: true :: true :: true :: payload =>
      let gp := BitString.decodeExactPairPayload payload
      Code.comp (programToCode gp.1) (programToCode gp.2)
  | false :: false :: false :: true :: payload =>
      Code.curry Code.left (BitString.toNatExact payload)
  | p =>
      additiveProgramToCode p
termination_by p => BitString.blen p
decreasing_by
  ·
    have hle := decodeExactPairPayload_fst_blen_le payload
    simp [BitString.blen] at hle ⊢
    omega
  ·
    have hle := decodeExactPairPayload_snd_blen_le payload
    simp [BitString.blen] at hle ⊢
    omega

private theorem programToCode_eq_step (p : Program) :
    programToCodeStep p ((programToCodeChildren p).map programToCode) = some (programToCode p) := by
  cases p with
  | nil =>
      simp [programToCodeStep, programToCodeChildren, programToCode, twoCodeCompOrZero]
  | cons b₁ t₁ =>
      cases t₁ with
      | nil =>
          cases b₁ <;> simp [programToCodeStep, programToCodeChildren, programToCode,
            twoCodeCompOrZero]
      | cons b₂ t₂ =>
          cases t₂ with
          | nil =>
              cases b₁ <;> cases b₂ <;>
                simp [programToCodeStep, programToCodeChildren, programToCode,
                  twoCodeCompOrZero]
          | cons b₃ t₃ =>
              cases t₃ with
              | nil =>
                  cases b₁ <;> cases b₂ <;> cases b₃ <;>
                    simp [programToCodeStep, programToCodeChildren, programToCode,
                      twoCodeCompOrZero]
              | cons b₄ payload =>
                  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
                    simp [programToCodeStep, programToCodeChildren, programToCode,
                      twoCodeCompOrZero]

/-- Reify a `Nat.Partrec.Code` back into a bitstring program. -/
def codeToProgram (c : Code) : Program :=
  additiveCodeToProgram c

private theorem programToCode_eq_additiveProgramToCode_of_notTagged
    (p : Program)
    (hPrefix : ∀ q : Program, p ≠ true :: true :: true :: true :: q)
    (hPostcompose : ∀ q : Program, p ≠ false :: true :: true :: true :: q)
    (hStored : ∀ q : Program, p ≠ false :: false :: false :: true :: q) :
    programToCode p = additiveProgramToCode p := by
  cases p with
  | nil =>
      simpa [programToCode]
  | cons b₁ t₁ =>
      cases t₁ with
      | nil =>
          simpa [programToCode]
      | cons b₂ t₂ =>
          cases t₂ with
          | nil =>
              simpa [programToCode]
          | cons b₃ t₃ =>
              cases t₃ with
              | nil =>
                  simpa [programToCode]
              | cons b₄ payload =>
                  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
                    all_goals
                      first
                      | simpa [programToCode]
                      | exfalso
                        exact hStored payload rfl
                      | exfalso
                        exact hPostcompose payload rfl
                      | exfalso
                        exact hPrefix payload rfl

private theorem programToCode_eq_additiveProgramToCode_on_code (c : Code) :
    programToCode (additiveCodeToProgram c) =
      additiveProgramToCode (additiveCodeToProgram c) := by
  refine programToCode_eq_additiveProgramToCode_of_notTagged (additiveCodeToProgram c) ?_ ?_ ?_
  · intro q h
    exact additiveCodeToProgram_ne_prefixReplaySentinel c q h
  · intro q h
    exact additiveCodeToProgram_ne_postcomposeSentinel c q h
  · intro q h
    exact additiveCodeToProgram_ne_storedValueSentinel c q h

@[simp] theorem programToCode_codeToProgram (c : Code) :
    programToCode (codeToProgram c) = c := by
  calc
    programToCode (codeToProgram c) =
        additiveProgramToCode (additiveCodeToProgram c) := by
      simpa [codeToProgram] using programToCode_eq_additiveProgramToCode_on_code c
    _ = c := additiveProgramToCode_additiveCodeToProgram c

theorem programToCode_primrec : Primrec programToCode := by
  refine Primrec.nat_omega_rec' programToCode
    (hm := Primrec.list_length)
    (hl := programToCodeChildren_primrec)
    (hg := programToCodeStep_primrec)
    ?_ ?_
  · intro p p' hp'
    cases p with
    | nil =>
        cases hp'
    | cons b₁ t₁ =>
        cases t₁ with
        | nil =>
            cases b₁ <;> simp [programToCodeChildren] at hp'
        | cons b₂ t₂ =>
            cases t₂ with
            | nil =>
                cases b₁ <;> cases b₂ <;> simp [programToCodeChildren] at hp'
            | cons b₃ t₃ =>
                cases t₃ with
                | nil =>
                    cases b₁ <;> cases b₂ <;> cases b₃ <;>
                      simp [programToCodeChildren] at hp'
                | cons b₄ payload =>
                    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
                      simp [programToCodeChildren] at hp'
                    · cases hp' with
                      | inl hmem =>
                          subst p'
                          have hle := decodeExactPairPayload_fst_blen_le payload
                          simp [BitString.blen] at hle ⊢
                          omega
                      | inr hp'' =>
                          subst p'
                          have hle := decodeExactPairPayload_snd_blen_le payload
                          simp [BitString.blen] at hle ⊢
                          omega
  · intro p
    simpa using programToCode_eq_step p

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
  simp [programToCode, prefixReplayPackedProgram, prefixReplaySentinel]

@[simp] theorem programToCode_postcomposePackedProgram (g p : Program) :
    programToCode (postcomposePackedProgram g p) =
      Code.comp (programToCode g) (programToCode p) := by
  simp [programToCode, postcomposePackedProgram, postcomposeSentinel]

@[simp] theorem programToCode_storedValuePackedProgram (p : Program) :
    programToCode (storedValuePackedProgram p) =
      Code.curry Code.left (BitString.toNatExact p) := by
  simp [programToCode, storedValuePackedProgram, storedValueSentinel]

@[simp] theorem blen_postcomposePackedProgram (g p : Program) :
    BitString.blen (postcomposePackedProgram g p) =
      BitString.blen p + BitString.blen g +
        (2 * BitString.blen (BitString.ofNatExact (BitString.blen g)) + 5) := by
  rw [postcomposePackedProgram, BitString.blen_append, BitString.blen_exactPairPayload]
  simp [postcomposeSentinel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

theorem blen_postcomposePackedProgram_le_of_blen_le
    {g p : Program} {k : Nat}
    (hg : BitString.blen g ≤ k) :
    BitString.blen (postcomposePackedProgram g p) ≤
      BitString.blen p + (k + (2 * BitString.blen (BitString.ofNat k) + 5)) := by
  rw [blen_postcomposePackedProgram]
  have henc :
      BitString.blen (BitString.ofNatExact (BitString.blen g)) ≤
        BitString.blen (BitString.ofNat k) := by
    exact le_trans
      (BitString.blen_ofNatExact_le_ofNat (BitString.blen g))
      (BitString.blen_ofNat_mono hg)
  omega

theorem runs_postcomposePackedProgram_of_runs
    {g p input mid output : BitString}
    (hp : runs p input mid)
    (hg : runs g mid output) :
    runs (postcomposePackedProgram g p) input output := by
  rw [runs_iff, programToCode_postcomposePackedProgram, Nat.Partrec.Code.eval]
  rw [runs_iff] at hp hg
  simpa [hp, hg]

@[simp] theorem blen_storedValuePackedProgram (p : Program) :
    BitString.blen (storedValuePackedProgram p) = BitString.blen p + 4 := by
  simp [storedValuePackedProgram, storedValueSentinel, BitString.blen]

@[simp] theorem runs_storedValuePackedProgram_iff (payload input output : BitString) :
    runs (storedValuePackedProgram payload) input output ↔ output = payload := by
  rw [runs_iff, programToCode_storedValuePackedProgram]
  constructor
  · intro h
    have h' :
        Part.some (BitString.toNatExact payload) =
          Part.some (BitString.toNatExact output) := by
      simpa [Nat.Partrec.Code.eval, Nat.Partrec.Code.eval_curry] using h
    apply BitString.toNatExact_injective
    simpa using h'.symm
  · intro h
    subst output
    simp [Nat.Partrec.Code.eval, Nat.Partrec.Code.eval_curry]

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
