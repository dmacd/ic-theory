import IcTheory.Computability.FinitePrefixDescriptions

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

/-- Specification of a fixed interpreter that runs two stored descriptions in sequence and
returns only the second-stage output. -/
def IsPostComposeInterpreter (u : Program) : Prop :=
  ∀ f s g r x y : Program,
    runs f (packedInput [] s) x →
      runs g (packedInput x r) y →
        runs u (packedInput [] (JointUpperPayload s f r g)) y

private theorem evalPostCompose_partrec :
    Nat.Partrec fun n =>
      Code.eval (Denumerable.ofNat Code (jointUpperFirstCodeNat n))
          (Nat.pair 0 (jointUpperResidualNat n)) >>= fun xNat =>
        Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
            (Nat.pair xNat (jointUpperSecondResidualNat n)) := by
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
  have hStep : _root_.Partrec₂ fun n xNat =>
      Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
        (Nat.pair xNat (jointUpperSecondResidualNat n)) := by
    simpa using hEval₂.to₂
  exact _root_.Partrec.nat_iff.1 (hEval₁.bind hStep)

theorem exists_postComposeInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n =
        Code.eval (Denumerable.ofNat Code (jointUpperFirstCodeNat n))
            (Nat.pair 0 (jointUpperResidualNat n)) >>= fun xNat =>
          Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
              (Nat.pair xNat (jointUpperSecondResidualNat n)) := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalPostCompose_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- Fixed interpreter used for postcomposition inside the swap-invariance proof. -/
noncomputable def postComposeInterpreterCode : Code :=
  Classical.choose exists_postComposeInterpreterCode

theorem eval_postComposeInterpreterCode (n : Nat) :
    Code.eval postComposeInterpreterCode n =
      Code.eval (Denumerable.ofNat Code (jointUpperFirstCodeNat n))
          (Nat.pair 0 (jointUpperResidualNat n)) >>= fun xNat =>
        Code.eval (Denumerable.ofNat Code (jointUpperSecondCodeNat n))
            (Nat.pair xNat (jointUpperSecondResidualNat n)) :=
  Classical.choose_spec exists_postComposeInterpreterCode n

/-- Concrete interpreter that decodes `JointUpperPayload`, executes the two stored descriptions in
sequence, and returns the second-stage output. -/
noncomputable def postComposeInterpreter : Program :=
  codeToProgram postComposeInterpreterCode

theorem postComposeInterpreter_isPostComposeInterpreter :
    IsPostComposeInterpreter postComposeInterpreter := by
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
  rw [postComposeInterpreter, runs_codeToProgram_iff, toNatExact_packedInput]
  simp [eval_postComposeInterpreterCode, jointUpperFirstCodeNat, jointUpperResidualNat,
    jointUpperSecondCodeNat, jointUpperSecondResidualNat, jointUpperDecoded, JointUpperPayload,
    hf', hg']

/-- Plain code that swaps the two components of a packed pair. -/
def swapPackedCode : Code :=
  Code.pair Code.right Code.left

/-- Plain code that extracts the left component of a packed pair. -/
def leftPackedCode : Code :=
  Code.comp Code.left Code.left

/-- Plain code that extracts the left component of an outer packed input and then swaps the
two components of that inner packed pair. -/
def swapJointCode : Code :=
  Code.comp swapPackedCode Code.left

/-- Fixed program used to turn a description of `⟨x, y⟩` into one of `⟨y, x⟩`. -/
noncomputable def swapJoint : Program :=
  codeToProgram swapJointCode

/-- Fixed program used to turn a description of `⟨x, y⟩` into one of `x`. -/
noncomputable def leftPacked : Program :=
  codeToProgram leftPackedCode

/-- Length of the fixed prefix program used for the swap post-processing step. -/
noncomputable def swapJointPrefixLength : Nat :=
  BitString.blen (BitString.pair swapJoint (BitString.e2 []))

@[simp] theorem runs_swapJoint_iff (x y : Program) :
    runs swapJoint (packedInput (packedInput x y) []) (packedInput y x) := by
  rw [swapJoint, runs_codeToProgram_iff]
  rw [toNatExact_packedInput, toNatExact_packedInput]
  have h :
      Code.eval swapJointCode (Nat.pair (Nat.pair (BitString.toNatExact x) (BitString.toNatExact y)) 0) =
        Part.some (Nat.pair (BitString.toNatExact y) (BitString.toNatExact x)) := by
    simp [Seq.seq, Part.bind, Part.assert, (· <$> ·), swapJointCode, swapPackedCode,
      Nat.Partrec.Code.eval]
    apply Part.ext'
    · constructor
      · intro _; trivial
      · intro _; exact ⟨trivial, trivial, trivial⟩
    · intro _ _
      rfl
  simpa using h

@[simp] theorem runs_leftPacked_iff (x y : Program) :
    runs leftPacked (packedInput (packedInput x y) []) x := by
  rw [leftPacked, runs_codeToProgram_iff]
  rw [toNatExact_packedInput, toNatExact_packedInput]
  simp [leftPackedCode, Nat.Partrec.Code.eval]

/-- Machine-readable payload for postcomposing a shortest description with a fixed program `g`
and empty residual. -/
noncomputable def fixedPostcomposePayload (s f g : Program) : Program :=
  JointUpperPayload s f [] g

/-- Prefix witness built from a shortest description and a fixed postcomposition layer. -/
noncomputable def fixedPostcomposeWitness (u g s f : Program) : Program :=
  BitString.pair u (BitString.e2 (fixedPostcomposePayload s f g))

/-- Constant contribution of the postcomposition interpreter and the fixed program `g`. -/
noncomputable def fixedPostcomposeWitnessOverhead (u g : Program) : Nat :=
  2 * BitString.blen u + 3 * BitString.blen (BitString.pair g (BitString.e2 [])) + 15

theorem prefixRuns_fixedPostcomposeWitness_of_runs {u g f s x y : Program}
    (hu : IsPostComposeInterpreter u)
    (hf : runs f (packedInput [] s) x)
    (hg : runs g (packedInput x []) y) :
    PrefixRuns (fixedPostcomposeWitness u g s f) [] y := by
  refine ⟨u, fixedPostcomposePayload s f g, rfl, ?_⟩
  exact hu f s g [] x y hf hg

private theorem blen_ofNat_le_logPenalty_add_const {m n c : Nat}
    (hm : m ≤ 3 * n + (c + 3)) :
    BitString.blen (BitString.ofNat m) ≤ logPenalty n + c + 5 := by
  let a : Nat := 2 ^ (c + 4)
  have ha16 : 16 ≤ a := by
    dsimp [a]
    calc
      16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (c + 4) := by
        exact Nat.pow_le_pow_right (by decide) (by omega)
  have ha3 : 3 ≤ a := Nat.le_trans (by decide : 3 ≤ 16) ha16
  have hac : c + 4 ≤ a := by
    dsimp [a]
    exact Nat.le_of_lt (show c + 4 < 2 ^ (c + 4) from Nat.lt_two_pow_self)
  have hscale : m ≤ (n + 1) * a - 1 := by
    calc
      m ≤ 3 * n + (c + 3) := hm
      _ ≤ a * n + (a - 1) := by
        have hmul : 3 * n ≤ a * n := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_right n ha3
        have hc : c + 3 ≤ a - 1 := by
          exact Nat.le_sub_one_of_lt (lt_of_lt_of_le (Nat.lt_succ_self (c + 3)) hac)
        omega
      _ = (n + 1) * a - 1 := by
        have ha1 : 1 ≤ a := Nat.le_trans (by decide : 1 ≤ 16) ha16
        calc
          a * n + (a - 1) = a * n + a - 1 := by rw [Nat.add_sub_assoc ha1]
          _ = n * a + a - 1 := by rw [Nat.mul_comm]
          _ = (n + 1) * a - 1 := by rw [Nat.add_mul, one_mul]
  have h :=
    blen_ofNat_le_logPenalty_add_of_le_twoPow_mul_succ_sub_one
      (m := m) (n := n) (k := c + 4) hscale
  omega

private theorem fixedPostcomposeWitness_length_bound_const {m n u c : Nat}
    (hm : m ≤ n + 2 * logPenalty n + (c + 3)) :
    2 * u + m + 2 * BitString.blen (BitString.ofNat m) + 2 ≤
      n + 4 * logPenalty n + (2 * u + 3 * c + 15) := by
  have hmLinear : m ≤ 3 * n + (c + 3) := by
    have hlog := logPenalty_le_self n
    omega
  have hlogm := blen_ofNat_le_logPenalty_add_const (c := c) hmLinear
  omega

private theorem blen_fixedPostcomposePayload_le_of_length {g f s : Program} {n : Nat}
    (hdesc : BitString.blen (BitString.pair f (BitString.e2 s)) = n) :
    BitString.blen (fixedPostcomposePayload s f g) ≤
      n + 2 * logPenalty n + (BitString.blen (BitString.pair g (BitString.e2 [])) + 3) := by
  have h := BitString.blen_exactQuadPayload_le_twoPrefixPrograms s f [] g
  dsimp [fixedPostcomposePayload, JointUpperPayload] at h ⊢
  rw [hdesc] at h
  have htail :
      2 * BitString.blen (BitString.ofNat n) + 1 ≤
        2 * logPenalty n + 3 := by
    have hlog := blen_ofNat_le_logPenalty_succ n
    omega
  calc
    BitString.blen (BitString.exactQuadPayload s f [] g) ≤
        n + BitString.blen (BitString.pair g (BitString.e2 [])) +
          (2 * BitString.blen (BitString.ofNat n) + 1) := h
    _ ≤ n + BitString.blen (BitString.pair g (BitString.e2 [])) + (2 * logPenalty n + 3) := by
      omega
    _ = n + 2 * logPenalty n + (BitString.blen (BitString.pair g (BitString.e2 [])) + 3) := by
      omega

/-- Composing a shortest prefix description with a fixed postprocessor adds only logarithmic
overhead. -/
theorem prefixComplexity_logLe_of_fixedPostcompose {u g x y : Program}
    (hu : IsPostComposeInterpreter u)
    (hg : runs g (packedInput x []) y) :
    LogLe (PrefixComplexity y) (PrefixComplexity x) (PrefixComplexity x) := by
  obtain ⟨p, hpLen, hpRuns⟩ := exists_program_forPrefixConditionalComplexity x []
  rcases hpRuns with ⟨f, s, hpEq, hf⟩
  let q : Program := fixedPostcomposeWitness u g s f
  have hqRuns : PrefixRuns q [] y := by
    simpa [q] using prefixRuns_fixedPostcomposeWitness_of_runs (u := u) (g := g) hu hf hg
  have hy : PrefixComplexity y ≤ BitString.blen q := by
    simpa [PrefixComplexity] using prefixConditionalComplexity_le_length hqRuns
  have hdesc : BitString.blen (BitString.pair f (BitString.e2 s)) = PrefixComplexity x := by
    rw [← hpEq, hpLen, PrefixComplexity]
  have hpayload :
      BitString.blen (fixedPostcomposePayload s f g) ≤
        PrefixComplexity x + 2 * logPenalty (PrefixComplexity x) +
          (BitString.blen (BitString.pair g (BitString.e2 [])) + 3) := by
    simpa [hdesc] using blen_fixedPostcomposePayload_le_of_length (g := g) (f := f) (s := s) hdesc
  have hshape :
      BitString.blen q =
        2 * BitString.blen u + BitString.blen (fixedPostcomposePayload s f g) +
          2 * BitString.blen (BitString.ofNat (BitString.blen (fixedPostcomposePayload s f g))) +
            2 := by
    simp [q, fixedPostcomposeWitness, BitString.blen_pair, BitString.blen_e2, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]
    omega
  have hqBound :
      BitString.blen q ≤
        PrefixComplexity x + 4 * logPenalty (PrefixComplexity x) +
          fixedPostcomposeWitnessOverhead u g := by
    rw [hshape]
    unfold fixedPostcomposeWitnessOverhead
    exact fixedPostcomposeWitness_length_bound_const
      (m := BitString.blen (fixedPostcomposePayload s f g))
      (n := PrefixComplexity x)
      (u := BitString.blen u)
      (c := BitString.blen (BitString.pair g (BitString.e2 [])))
      hpayload
  exact ⟨4, fixedPostcomposeWitnessOverhead u g, le_trans hy hqBound⟩

/-- One-sided swap invariance for joint prefix complexity. -/
theorem jointSwapLogLe (x y : Program) :
    LogLe (JointComplexity x y) (JointComplexity y x) (JointComplexity y x) := by
  simpa [JointComplexity] using
    (prefixComplexity_logLe_of_fixedPostcompose
      (u := postComposeInterpreter)
      (g := swapJoint)
      (x := packedInput y x)
      (y := packedInput x y)
      postComposeInterpreter_isPostComposeInterpreter
      (by simpa using runs_swapJoint_iff y x))

/-- Left projection from joint complexity costs only logarithmic overhead. -/
theorem jointLeftProjectionLogLe (x y : Program) :
    LogLe (PrefixComplexity x) (JointComplexity x y) (JointComplexity x y) := by
  simpa [JointComplexity] using
    (prefixComplexity_logLe_of_fixedPostcompose
      (u := postComposeInterpreter)
      (g := leftPacked)
      (x := packedInput x y)
      (y := x)
      postComposeInterpreter_isPostComposeInterpreter
      (by simpa using runs_leftPacked_iff x y))

private theorem jointRightHeaderBound {x y : Program} {c d : Nat} :
    BitString.blen
        (BitString.ofNat
          ((JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x) +
            3 * logPenalty (JointComplexity x y) + 4)) ≤
      logPenalty (JointComplexity x y) + (c + d + 6) := by
  let n : Nat := JointComplexity x y
  let m : Nat := (n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4
  let a : Nat := 2 ^ (c + d + 5)
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
  have habig : c + d + 5 ≤ a := by
    dsimp [a]
    exact Nat.le_of_lt (show c + d + 5 < 2 ^ (c + d + 5) from Nat.lt_two_pow_self)
  have hac : c + 4 ≤ a := by
    exact le_trans (by omega) habig
  have had : d + 5 ≤ a := by
    exact le_trans (by omega) habig
  have hconst : d + 4 ≤ a - 1 := by
    exact Nat.le_sub_one_of_lt (lt_of_lt_of_le (Nat.lt_succ_self (d + 4)) had)
  have hm : m ≤ (n + 1) * a - 1 := by
    have hsub : n + c * logPenalty n + d - PrefixComplexity x ≤ n + c * logPenalty n + d := by
      exact Nat.sub_le _ _
    have hlog := logPenalty_le_self n
    have hc : c * logPenalty n ≤ c * n := Nat.mul_le_mul_left c hlog
    have h3 : 3 * logPenalty n ≤ 3 * n := Nat.mul_le_mul_left 3 hlog
    calc
      m ≤ n + c * logPenalty n + d + 3 * logPenalty n + 4 := by
        dsimp [m]
        omega
      _ ≤ n + c * n + d + 3 * n + 4 := by
        omega
      _ = c * n + 4 * n + (d + 4) := by
        omega
      _ = (c + 4) * n + (d + 4) := by
        rw [Nat.add_mul]
      _ ≤ a * n + (a - 1) := by
        have hmul : (c + 4) * n ≤ a * n := Nat.mul_le_mul_right n hac
        exact Nat.add_le_add hmul hconst
      _ = (n + 1) * a - 1 := by
        calc
          a * n + (a - 1) = a * n + a - 1 := by rw [Nat.add_sub_assoc ha1]
          _ = n * a + a - 1 := by rw [Nat.mul_comm]
          _ = (n + 1) * a - 1 := by rw [Nat.add_mul, one_mul]
  have hblen :=
    blen_ofNat_le_logPenalty_add_of_le_twoPow_mul_succ_sub_one
      (m := m) (n := n) (k := c + d + 5) hm
  dsimp [m, n] at hblen ⊢
  omega

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

/-- Joint prefix complexity is swap-invariant up to logarithmic slack at the natural max scale. -/
theorem jointSwapInvariantAt_max (x y : Program) :
    JointSwapInvariantAt (max (JointComplexity x y) (JointComplexity y x)) x y := by
  refine ⟨?_, ?_⟩
  · exact logLe_of_scale_le (jointSwapLogLe x y) (le_max_right _ _)
  · exact logLe_of_scale_le (jointSwapLogLe y x) (le_max_left _ _)

theorem jointSwapInvariantAt_of_bounds {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n)
    (hyx : JointComplexity y x ≤ n) :
    JointSwapInvariantAt n x y := by
  exact logEq_of_scale_le (jointSwapInvariantAt_max x y) (max_le_iff.mpr ⟨hxy, hyx⟩)

/-- Count-bound assumption for the fixed-`x` candidate family underlying the lower chain rule. -/
def JointRightCountBoundAt (n : Nat) (x _y : Program) : Prop :=
  ∃ c d : Nat,
    (jointRightOutputsUpToLength x n).length ≤ 2 ^ (n + c * logPenalty n + d - PrefixComplexity x)

/-- A heavy-left enumerator gives the sharp fixed-`x` count bound with explicit logarithmic
slack, so the lower-chain rule no longer needs the count theorem as a separate hypothesis. -/
theorem jointRightCountBoundAt_of_jointLeftCountEnumerator {u x y : Program} {n : Nat}
    (hu : IsJointLeftCountEnumerator u) :
    JointRightCountBoundAt n x y := by
  refine ⟨8, 2 * BitString.blen u + 25, ?_⟩
  simpa using
    (length_jointRightOutputsUpToLength_le_of_jointLeftCountEnumerator
      (u := u) (x := x) (n := n) hu)

/-- A fixed enumerator plus a sharp count bound, a logarithmic header bound, and a projection
bound for `K(x)` give the lower chain rule at the natural scale `K(x, y)`. -/
theorem jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_and_header
    {u x y : Program} {c d e k t : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x (JointComplexity x y)).length ≤
        2 ^ (JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x))
    (hheader :
      BitString.blen
          (BitString.ofNat
            ((JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x) +
              3 * logPenalty (JointComplexity x y) + 4)) ≤
        logPenalty (JointComplexity x y) + e)
    (hpx :
      PrefixComplexity x ≤
        JointComplexity x y + k * logPenalty (JointComplexity x y) + t) :
    JointLowerChainRuleAt (JointComplexity x y) x y := by
  let n : Nat := JointComplexity x y
  have hsum :=
    prefixComplexity_add_prefixConditionalComplexity_le_of_jointRightEnumerator_of_count
      (u := u) (x := x) (y := y) (n := n) (c := c) (d := d) (k := k) (t := t)
      hu hcount (by simpa [n] using hpx) le_rfl
  have hheader' :
      BitString.blen
          (BitString.ofNat
            ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) ≤
        logPenalty n + e := by
    simpa [n] using hheader
  have htwice :
      2 * BitString.blen
          (BitString.ofNat
            ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) ≤
        2 * (logPenalty n + e) := by
    exact Nat.mul_le_mul_left 2 hheader'
  have hsum' :
      PrefixComplexity x + PrefixConditionalComplexity y x ≤
        n + (c + k + 3) * logPenalty n + (d + t) + 2 * (logPenalty n + e) +
          (2 * BitString.blen u + 6) := by
    calc
      PrefixComplexity x + PrefixConditionalComplexity y x ≤
          n + (c + k + 3) * logPenalty n + (d + t) +
            2 * BitString.blen
              (BitString.ofNat
                ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
            (2 * BitString.blen u + 6) := hsum
      _ ≤ n + (c + k + 3) * logPenalty n + (d + t) + 2 * (logPenalty n + e) +
            (2 * BitString.blen u + 6) := by
        calc
          n + (c + k + 3) * logPenalty n + (d + t) +
              2 * BitString.blen
                (BitString.ofNat
                  ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
              (2 * BitString.blen u + 6)
              =
              n + (c + k + 3) * logPenalty n + (d + t) +
                (2 * BitString.blen
                  (BitString.ofNat
                    ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
                  (2 * BitString.blen u + 6)) := by
            omega
          _ ≤ n + (c + k + 3) * logPenalty n + (d + t) +
                (2 * (logPenalty n + e) + (2 * BitString.blen u + 6)) := by
            exact Nat.add_le_add_left
              (Nat.add_le_add_right htwice (2 * BitString.blen u + 6))
              (n + (c + k + 3) * logPenalty n + (d + t))
          _ =
              n + (c + k + 3) * logPenalty n + (d + t) + 2 * (logPenalty n + e) +
                (2 * BitString.blen u + 6) := by
            omega
  have hmul :
      (c + k + 5) * logPenalty n = (c + k + 3) * logPenalty n + 2 * logPenalty n := by
    have hck : c + k + 5 = (c + k + 3) + 2 := by omega
    rw [hck, Nat.add_mul]
  have hsum'' :
      PrefixComplexity x + PrefixConditionalComplexity y x ≤
        n + (c + k + 5) * logPenalty n + (d + t + 2 * e + (2 * BitString.blen u + 6)) := by
    calc
      PrefixComplexity x + PrefixConditionalComplexity y x ≤
          n + (c + k + 3) * logPenalty n + (d + t) + 2 * (logPenalty n + e) +
            (2 * BitString.blen u + 6) := hsum'
      _ = n + (c + k + 5) * logPenalty n + (d + t + 2 * e + (2 * BitString.blen u + 6)) := by
        rw [hmul, Nat.mul_add]
        omega
  refine ⟨c + k + 5, d + t + 2 * e + (2 * BitString.blen u + 6), ?_⟩
  simpa [n] using hsum''

theorem jointLowerChainRuleAt_of_jointRightEnumerator_of_count_and_header_of_scale_le
    {u x y : Program} {n c d e k t : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x (JointComplexity x y)).length ≤
        2 ^ (JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x))
    (hheader :
      BitString.blen
          (BitString.ofNat
            ((JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x) +
              3 * logPenalty (JointComplexity x y) + 4)) ≤
        logPenalty (JointComplexity x y) + e)
    (hpx :
      PrefixComplexity x ≤
        JointComplexity x y + k * logPenalty (JointComplexity x y) + t)
    (hscale : JointComplexity x y ≤ n) :
    JointLowerChainRuleAt n x y := by
  exact logLe_of_scale_le
    (jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_and_header
      (u := u) (x := x) (y := y) (c := c) (d := d) (e := e) (k := k) (t := t)
      hu hcount hheader hpx)
    hscale

/-- The left projection bound `K(x) ≤ K(x, y) + O(log K(x, y))` is available from the concrete
postcomposition machinery, so the lower-chain rule needs only the sharp count and header bounds
as extra hypotheses. -/
theorem jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_and_header_of_leftProjection
    {u x y : Program} {c d e : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x (JointComplexity x y)).length ≤
        2 ^ (JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x))
    (hheader :
      BitString.blen
          (BitString.ofNat
            ((JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x) +
              3 * logPenalty (JointComplexity x y) + 4)) ≤
        logPenalty (JointComplexity x y) + e) :
    JointLowerChainRuleAt (JointComplexity x y) x y := by
  obtain ⟨k, t, hpx⟩ := jointLeftProjectionLogLe x y
  exact jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_and_header
    (u := u) (x := x) (y := y) (c := c) (d := d) (e := e) (k := k) (t := t)
    hu hcount hheader hpx

theorem jointLowerChainRuleAt_of_jointRightEnumerator_of_count_and_header_of_leftProjection_of_scale_le
    {u x y : Program} {n c d e : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x (JointComplexity x y)).length ≤
        2 ^ (JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x))
    (hheader :
      BitString.blen
          (BitString.ofNat
            ((JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x) +
              3 * logPenalty (JointComplexity x y) + 4)) ≤
        logPenalty (JointComplexity x y) + e)
    (hscale : JointComplexity x y ≤ n) :
    JointLowerChainRuleAt n x y := by
  exact logLe_of_scale_le
    (jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_and_header_of_leftProjection
      (u := u) (x := x) (y := y) (c := c) (d := d) (e := e)
      hu hcount hheader)
    hscale

/-- The generic header bound is automatic, so only the sharp fixed-`x` count bound remains as
an extra lower-chain hypothesis once left projection is available. -/
theorem jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_of_leftProjection
    {u x y : Program} {c d : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x (JointComplexity x y)).length ≤
        2 ^ (JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x)) :
    JointLowerChainRuleAt (JointComplexity x y) x y := by
  exact
    jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_and_header_of_leftProjection
      (u := u) (x := x) (y := y) (c := c) (d := d) (e := c + d + 6)
      hu hcount jointRightHeaderBound

theorem jointLowerChainRuleAt_of_jointRightEnumerator_of_count_of_leftProjection_of_scale_le
    {u x y : Program} {n c d : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x (JointComplexity x y)).length ≤
        2 ^ (JointComplexity x y + c * logPenalty (JointComplexity x y) + d - PrefixComplexity x))
    (hscale : JointComplexity x y ≤ n) :
    JointLowerChainRuleAt n x y := by
  exact logLe_of_scale_le
    (jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_of_leftProjection
      (u := u) (x := x) (y := y) (c := c) (d := d) hu hcount)
    hscale

theorem jointLowerChainRuleAt_complexityScale_of_jointRightCountBoundAt_of_leftProjection
    {u x y : Program}
    (hu : IsJointRightEnumerator u)
    (hcount : JointRightCountBoundAt (JointComplexity x y) x y) :
    JointLowerChainRuleAt (JointComplexity x y) x y := by
  rcases hcount with ⟨c, d, hcount⟩
  exact
    jointLowerChainRuleAt_complexityScale_of_jointRightEnumerator_of_count_of_leftProjection
      (u := u) (x := x) (y := y) (c := c) (d := d) hu hcount

theorem jointLowerChainRuleAt_of_jointRightCountBoundAt_of_leftProjection_of_scale_le
    {u x y : Program} {n : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount : JointRightCountBoundAt (JointComplexity x y) x y)
    (hscale : JointComplexity x y ≤ n) :
    JointLowerChainRuleAt n x y := by
  exact logLe_of_scale_le
    (jointLowerChainRuleAt_complexityScale_of_jointRightCountBoundAt_of_leftProjection
      (u := u) (x := x) (y := y) hu hcount)
    hscale

/-- The heavy-left discovery machine discharges the sharp fixed-`x` count bound needed for the
lower chain rule. -/
theorem jointRightCountBoundAt_concrete {x y : Program} {n : Nat} :
    JointRightCountBoundAt n x y := by
  exact jointRightCountBoundAt_of_jointLeftCountEnumerator
    (u := jointLeftCountEnumerator) (x := x) (y := y) (n := n)
    jointLeftCountEnumerator_isJointLeftCountEnumerator

/-- Concrete lower-chain theorem from the fixed right/left enumeration programs. -/
theorem jointLowerChainRuleAt_concrete_of_scale_le {x y : Program} {n : Nat}
    (hscale : JointComplexity x y ≤ n) :
    JointLowerChainRuleAt n x y := by
  exact jointLowerChainRuleAt_of_jointRightCountBoundAt_of_leftProjection_of_scale_le
    (u := jointRightEnumerator) (x := x) (y := y)
    jointRightEnumerator_isJointRightEnumerator
    (jointRightCountBoundAt_concrete (x := x) (y := y) (n := JointComplexity x y))
    hscale

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
