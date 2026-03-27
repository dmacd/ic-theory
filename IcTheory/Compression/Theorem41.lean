import IcTheory.Compression.Section4
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- Total search budget allocated in phase `i` by the current concrete Section 4 schedule. -/
def phaseTotalBudget (i : Nat) : Nat :=
  ((phasePrograms i).map (phaseBudget i)).sum

/-- Total search budget allocated to a fixed node up to and including phase `i`. -/
def nodeBudgetUntil (a : Program) : Nat → Nat
  | 0 => phaseBudget 0 a
  | i + 1 => nodeBudgetUntil a i + phaseBudget (i + 1) a

theorem phasePrograms_succ (i : Nat) :
    phasePrograms (i + 1) = phasePrograms i ++ BitString.allOfLength i := by
  cases i with
  | zero =>
      simp [phasePrograms, BitString.allUpToLength]
  | succ i =>
      simp [phasePrograms, BitString.allUpToLength]

private theorem phaseBudget_eq_zero_of_length_ge {a : Program} {i : Nat}
    (h : i ≤ BitString.blen a) :
    phaseBudget i a = 0 := by
  simp [phaseBudget, not_lt.mpr h]

private theorem phaseBudget_eq_pow_of_length_lt {a : Program} {i : Nat}
    (h : BitString.blen a < i) :
    phaseBudget i a = 2 ^ (i - BitString.blen a) := by
  simp [phaseBudget, h]

private theorem phaseBudget_succ_eq_double {a : Program} {i : Nat}
    (h : BitString.blen a < i) :
    phaseBudget (i + 1) a = 2 * phaseBudget i a := by
  rw [phaseBudget_eq_pow_of_length_lt (show BitString.blen a < i + 1 by omega)]
  rw [phaseBudget_eq_pow_of_length_lt h]
  rw [show i + 1 - BitString.blen a = (i - BitString.blen a) + 1 by omega, Nat.pow_succ]
  omega

private theorem sum_phaseBudget_succ_eq_double {l : List Program} {i : Nat}
    (hl : ∀ a ∈ l, BitString.blen a < i) :
    (l.map (phaseBudget (i + 1))).sum = 2 * (l.map (phaseBudget i)).sum := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      have ha : BitString.blen a < i := hl a (by simp)
      have hl' : ∀ b ∈ l, BitString.blen b < i := by
        intro b hb
        exact hl b (by simp [hb])
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih hl']
      rw [phaseBudget_succ_eq_double ha]
      omega

private theorem sum_phaseBudget_allOfLength_succ (i : Nat) :
    ((BitString.allOfLength i).map (phaseBudget (i + 1))).sum = 2 ^ (i + 1) := by
  have hrep :
      (BitString.allOfLength i).map (phaseBudget (i + 1)) =
        List.replicate (BitString.allOfLength i).length 2 := by
    have hrep' :
        (BitString.allOfLength i).map (phaseBudget (i + 1)) =
          List.replicate (((BitString.allOfLength i).map (phaseBudget (i + 1))).length) 2 := by
      refine (List.eq_replicate_length).2 ?_
      intro v hv
      rcases List.mem_map.1 hv with ⟨a, ha, rfl⟩
      have hlen : BitString.blen a = i := BitString.mem_allOfLength_iff.1 ha
      rw [phaseBudget_eq_pow_of_length_lt (show BitString.blen a < i + 1 by omega)]
      rw [hlen]
      simp
    simpa [List.length_map] using hrep'
  rw [hrep, List.sum_replicate, BitString.length_allOfLength]
  simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

@[simp] theorem phaseTotalBudget_zero : phaseTotalBudget 0 = 0 := by
  simp [phaseTotalBudget, phasePrograms, phaseBudget]

theorem phaseTotalBudget_succ (i : Nat) :
    phaseTotalBudget (i + 1) = 2 * phaseTotalBudget i + 2 ^ (i + 1) := by
  rw [phaseTotalBudget, phasePrograms_succ, List.map_append, List.sum_append]
  have hold :
      ((phasePrograms i).map (phaseBudget (i + 1))).sum =
        2 * phaseTotalBudget i := by
    refine sum_phaseBudget_succ_eq_double ?_
    intro a ha
    exact mem_phasePrograms_iff.1 ha
  rw [hold, sum_phaseBudget_allOfLength_succ]

theorem phaseTotalBudget_eq (i : Nat) :
    phaseTotalBudget i = i * 2 ^ i := by
  induction i with
  | zero =>
      simp [phaseTotalBudget_zero]
  | succ i ih =>
      rw [phaseTotalBudget_succ, ih, Nat.pow_succ]
      calc
        2 * (i * 2 ^ i) + 2 ^ i * 2 = i * (2 ^ i * 2) + 1 * (2 ^ i * 2) := by ac_rfl
        _ = (i + 1) * (2 ^ i * 2) := by
          simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _ = (i + 1) * 2 ^ (i + 1) := by rw [Nat.pow_succ]

@[simp] theorem nodeBudgetUntil_zero (a : Program) :
    nodeBudgetUntil a 0 = 0 := by
  simp [nodeBudgetUntil, phaseBudget]

theorem nodeBudgetUntil_eq_zero_of_le {a : Program} {i : Nat}
    (h : i ≤ BitString.blen a) :
    nodeBudgetUntil a i = 0 := by
  induction i with
  | zero =>
      simp [nodeBudgetUntil, phaseBudget]
  | succ i ih =>
      rw [nodeBudgetUntil, ih (Nat.le_of_succ_le h), phaseBudget_eq_zero_of_length_ge h]

theorem nodeBudgetUntil_eq_closed (a : Program) (i : Nat) :
    nodeBudgetUntil a i =
      if i ≤ BitString.blen a then 0 else 2 ^ (i - BitString.blen a + 1) - 2 := by
  induction i with
  | zero =>
      simp [nodeBudgetUntil, phaseBudget]
  | succ i ih =>
      by_cases hcur : i + 1 ≤ BitString.blen a
      · have hprev : i ≤ BitString.blen a := Nat.le_of_succ_le hcur
        have ih0 : nodeBudgetUntil a i = 0 := by
          simpa [if_pos hprev] using ih
        rw [nodeBudgetUntil, ih0, phaseBudget_eq_zero_of_length_ge hcur]
        simp [hcur]
      · have hgt : BitString.blen a < i + 1 := lt_of_not_ge hcur
        by_cases hprev : i ≤ BitString.blen a
        · have heq : i = BitString.blen a := by omega
          have hphase : phaseBudget (i + 1) a = 2 := by
            rw [phaseBudget_eq_pow_of_length_lt hgt]
            rw [heq]
            simp
          have ih0 : nodeBudgetUntil a i = 0 := by
            simpa [if_pos hprev] using ih
          rw [nodeBudgetUntil, ih0, hphase]
          simp [hcur, heq]
        · have hphase : phaseBudget (i + 1) a = 2 ^ (i + 1 - BitString.blen a) :=
            phaseBudget_eq_pow_of_length_lt hgt
          have ih1 : nodeBudgetUntil a i = 2 ^ (i - BitString.blen a + 1) - 2 := by
            simpa [if_neg hprev] using ih
          have hphase' : phaseBudget (i + 1) a = 2 ^ (i - BitString.blen a + 1) := by
            rw [hphase]
            rw [show i + 1 - BitString.blen a = i - BitString.blen a + 1 by omega]
          rw [nodeBudgetUntil, ih1, hphase']
          simp [hcur]
          rw [show i + 1 - BitString.blen a + 1 = (i - BitString.blen a + 1) + 1 by omega,
            Nat.pow_succ]
          omega

theorem nodeBudgetUntil_eq_of_lt {a : Program} {i : Nat}
    (h : BitString.blen a < i) :
    nodeBudgetUntil a i = 2 ^ (i - BitString.blen a + 1) - 2 := by
  simpa [if_neg (not_le.mpr h)] using nodeBudgetUntil_eq_closed a i

theorem nodeBudgetUntil_lt_pow {a : Program} {i : Nat}
    (h : BitString.blen a < i) :
    nodeBudgetUntil a i < 2 ^ (i - BitString.blen a + 1) := by
  rw [nodeBudgetUntil_eq_of_lt h]
  have hpow : 0 < 2 ^ (i - BitString.blen a + 1) := by
    exact pow_pos (show 0 < 2 by decide) _
  omega

theorem pow_le_nodeBudgetUntil {a : Program} {i : Nat}
    (h : BitString.blen a + 1 < i) :
    2 ^ (i - BitString.blen a) ≤ nodeBudgetUntil a i := by
  rw [nodeBudgetUntil_eq_of_lt (show BitString.blen a < i by omega)]
  rw [show i - BitString.blen a + 1 = (i - BitString.blen a) + 1 by omega, Nat.pow_succ]
  have hpow : 2 ≤ 2 ^ (i - BitString.blen a) := by
    calc
      2 = 2 ^ 1 := by simp
      _ ≤ 2 ^ (i - BitString.blen a) := by
        exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Abstract prefix-style phase-mass hypothesis used in the paper's Lemma 4.1 proof. The
upper bound is the Kraft-type `2^(n+1)` estimate, while the lower bound records the contribution
of the shortest codeword `amin`. -/
structure PrefixPhaseModel (total : Nat → Nat) (amin : Nat) : Prop where
  upper : ∀ n, total n ≤ 2 ^ (n + 1)
  lower : ∀ {n}, amin ≤ n → 2 ^ (n - amin) ≤ total n

/-- `NodeBudgetWitness a τ n` means phase `n + 1` is the first phase by which the current
schedule has allocated at least `τ` steps to node `a`. -/
def NodeBudgetWitness (a : Program) (τ n : Nat) : Prop :=
  nodeBudgetUntil a n < τ ∧ τ ≤ nodeBudgetUntil a (n + 1)

theorem nodeBudgetWitness_pos {a : Program} {τ n : Nat}
    (hw : NodeBudgetWitness a τ n) :
    0 < τ := by
  exact lt_of_le_of_lt (Nat.zero_le _) hw.1

theorem length_le_of_nodeBudgetWitness {a : Program} {τ n : Nat}
    (hw : NodeBudgetWitness a τ n) :
    BitString.blen a ≤ n := by
  by_contra hlen
  have hphase0 : nodeBudgetUntil a (n + 1) = 0 := by
    exact nodeBudgetUntil_eq_zero_of_le (a := a) (i := n + 1) (by omega)
  have hτle : τ ≤ 0 := by
    simpa [hphase0] using hw.2
  have hτ0 : τ = 0 := le_antisymm hτle (Nat.zero_le _)
  exact (Nat.ne_of_gt (nodeBudgetWitness_pos hw)) hτ0

theorem nodeBudgetWitness_pow_le_succ {a : Program} {τ n : Nat}
    (hw : NodeBudgetWitness a τ n) :
    2 ^ (n - BitString.blen a + 1) ≤ τ + 1 := by
  have hlen : BitString.blen a ≤ n := length_le_of_nodeBudgetWitness hw
  rcases eq_or_lt_of_le hlen with rfl | hlt
  · have hzero : nodeBudgetUntil a (BitString.blen a) = 0 :=
        nodeBudgetUntil_eq_zero_of_le (a := a) (i := BitString.blen a) le_rfl
    have hτ0 : 0 < τ := by
      simpa [hzero] using hw.1
    have hτ1 : 1 ≤ τ := Nat.succ_le_of_lt hτ0
    simpa using Nat.succ_le_succ hτ1
  · have hclosed : nodeBudgetUntil a n = 2 ^ (n - BitString.blen a + 1) - 2 :=
      nodeBudgetUntil_eq_of_lt hlt
    have hlt' : 2 ^ (n - BitString.blen a + 1) - 2 < τ := by
      simpa [hclosed] using hw.1
    omega

/-- Abstract upper half of the paper's Lemma 4.1, reduced to the prefix-style phase-mass model.
Because the current concrete phase indexing starts giving a node two steps at its first active
phase, the clean bound comes out as `2^(|a|+1) * (τ + 1)`. -/
theorem lemma41_upper_of_prefixPhaseModel
    {total : Nat → Nat} {amin : Nat} {a : Program} {τ n : Nat}
    (hmodel : PrefixPhaseModel total amin)
    (hw : NodeBudgetWitness a τ n) :
    total (n + 1) ≤ 2 ^ (BitString.blen a + 1) * (τ + 1) := by
  have hupper := hmodel.upper (n + 1)
  have hlen : BitString.blen a ≤ n := length_le_of_nodeBudgetWitness hw
  have hpow : 2 ^ (n - BitString.blen a + 1) ≤ τ + 1 :=
    nodeBudgetWitness_pow_le_succ hw
  calc
    total (n + 1) ≤ 2 ^ (n + 2) := by
      simpa using hupper
    _ = 2 ^ (BitString.blen a + 1) * 2 ^ (n - BitString.blen a + 1) := by
      have hexp : n + 2 = BitString.blen a + 1 + (n - BitString.blen a + 1) := by
        omega
      rw [hexp, Nat.pow_add]
    _ ≤ 2 ^ (BitString.blen a + 1) * (τ + 1) := by
      exact Nat.mul_le_mul_left _ hpow

/-- Abstract lower half of the paper's Lemma 4.1 with the fractional `2^{-1}` factor cleared:
`2^(|a|-|amin|) * τ < 2 * T`. This avoids leaving the natural-number setting while keeping the
same content as the paper bound. -/
theorem lemma41_lower_of_prefixPhaseModel
    {total : Nat → Nat} {amin : Nat} {a : Program} {τ n : Nat}
    (hmodel : PrefixPhaseModel total amin)
    (hmin : amin ≤ BitString.blen a)
    (hw : NodeBudgetWitness a τ n) :
    2 ^ (BitString.blen a - amin) * τ < 2 * total (n + 1) := by
  have hlen : BitString.blen a ≤ n := length_le_of_nodeBudgetWitness hw
  rcases hw with ⟨hwPrev, hwNext⟩
  have hlt : BitString.blen a < n + 1 := by omega
  have hnode : nodeBudgetUntil a (n + 1) = 2 ^ (n + 1 - BitString.blen a + 1) - 2 :=
    nodeBudgetUntil_eq_of_lt hlt
  have hτpow : τ < 2 ^ (n + 1 - BitString.blen a + 1) := by
    rw [hnode] at hwNext
    omega
  have hmul :
      2 ^ (BitString.blen a - amin) * τ <
        2 ^ (BitString.blen a - amin) * 2 ^ (n + 1 - BitString.blen a + 1) := by
    exact Nat.mul_lt_mul_of_pos_left hτpow (pow_pos (show 0 < 2 by decide) _)
  have hphaseLower : 2 ^ (n + 1 - amin) ≤ total (n + 1) :=
    hmodel.lower (n := n + 1) (by omega)
  have hscale :
      2 ^ (BitString.blen a - amin) * 2 ^ (n + 1 - BitString.blen a + 1) ≤ 2 * total (n + 1) := by
    calc
      2 ^ (BitString.blen a - amin) * 2 ^ (n + 1 - BitString.blen a + 1) =
          2 ^ (n + 1 - amin) * 2 := by
        rw [← Nat.pow_add]
        have hexp :
            BitString.blen a - amin + (n + 1 - BitString.blen a + 1) = n + 1 - amin + 1 := by
          omega
        rw [hexp, Nat.pow_succ]
      _ ≤ total (n + 1) * 2 := by
        exact Nat.mul_le_mul_right 2 hphaseLower
      _ = 2 * total (n + 1) := by rw [Nat.mul_comm]
  exact lt_of_lt_of_le hmul hscale

/-- Packaged current-form version of Lemma 4.1 under the abstract prefix-style phase model. -/
theorem lemma41_of_prefixPhaseModel
    {total : Nat → Nat} {amin : Nat} {a : Program} {τ n : Nat}
    (hmodel : PrefixPhaseModel total amin)
    (hmin : amin ≤ BitString.blen a)
    (hw : NodeBudgetWitness a τ n) :
    total (n + 1) ≤ 2 ^ (BitString.blen a + 1) * (τ + 1) ∧
      2 ^ (BitString.blen a - amin) * τ < 2 * total (n + 1) := by
  exact ⟨
    lemma41_upper_of_prefixPhaseModel hmodel hw,
    lemma41_lower_of_prefixPhaseModel hmodel hmin hw
  ⟩

/-- The current concrete Section 4 schedule is not yet the paper's prefix-code schedule: its
total phase mass grows like `n * 2^n`, so it violates the prefix-style upper bound already at
phase `3`. -/
theorem not_prefixPhaseModel_phaseTotalBudget (amin : Nat) :
    ¬ PrefixPhaseModel phaseTotalBudget amin := by
  intro hmodel
  have hupper := hmodel.upper 3
  rw [phaseTotalBudget_eq] at hupper
  norm_num at hupper

theorem bCompressionSchemeStep_isAutoencoderStep
    {b : Nat} {x f g r : Program}
    (hstep : BCompressionSchemeStep b x f g r) :
    AutoencoderStep x g f r := by
  exact ⟨hstep.mapRuns, hstep.featureRuns, hstep.compression⟩

theorem searchAutoencoderAccepts_of_bCompressionSchemeStep
    {b : Nat} {x f g r : Program}
    (hstep : BCompressionSchemeStep b x f g r) :
    SearchAutoencoderAccepts x (autoencoderPayload g f) := by
  exact (searchAutoencoderAccepts_iff (x := x) (g := g) (f := f)).2
    ⟨r, bCompressionSchemeStep_isAutoencoderStep hstep⟩

private theorem exists_aliceBranch_extension_of_incrementalBCompressionScheme
    {b : Nat} {x current rs : Program} {startNode : AliceNode} {fs gs : List Program}
    (hstart : IsAliceBranch x startNode)
    (hcurrent : startNode.residual = current)
    (hchain : IsIncrementalBCompressionScheme b current fs gs rs) :
    ∃ node, IsAliceBranch x node ∧ node.residual = rs ∧ node.features = startNode.features ++ fs := by
  induction hchain generalizing startNode with
  | stop_small current hsmall =>
      refine ⟨startNode, hstart, ?_, ?_⟩
      · simpa [hcurrent]
      · simp
  | stop_incompressible current hnot =>
      refine ⟨startNode, hstart, ?_, ?_⟩
      · simpa [hcurrent]
      · simp
  | @cons current f g r rs fs gs hbig hbc hstep hrest ih =>
      have hauto : AutoencoderStep startNode.residual g f r := by
        simpa [hcurrent] using bCompressionSchemeStep_isAutoencoderStep hstep
      let next := startNode.extend r f
      have hnext : IsAliceBranch x next := by
        exact IsAliceBranch.step hstart hauto
      obtain ⟨node, hnode, hres, hfeatures⟩ := ih hnext rfl
      refine ⟨node, hnode, hres, ?_⟩
      simpa [next, List.append_assoc] using hfeatures

/-- Every incremental `b`-compression scheme determines a concrete ALICE branch with the same
terminal residual and feature sequence. This is the semantic half of Theorem 4.1, separated from
the later runtime analysis. -/
theorem exists_aliceBranch_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    ∃ node, IsAliceBranch x node ∧ node.residual = rs ∧ node.features = fs := by
  simpa using
    (exists_aliceBranch_extension_of_incrementalBCompressionScheme
      (x := x)
      (current := x)
      (startNode := AliceNode.root x)
      (fs := fs)
      (gs := gs)
      (hstart := IsAliceBranch.root)
      (hcurrent := rfl)
      hchain)

/-- The branch node extracted from an incremental compression scheme carries exactly the concrete
description object `D_s = ⟨s, r_s, f_s, ..., f_1⟩`. -/
theorem exists_aliceBranch_description_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs := by
  obtain ⟨node, hnode, hres, hfeatures⟩ :=
    exists_aliceBranch_of_incrementalBCompressionScheme hchain
  refine ⟨node, hnode, ?_⟩
  simp [AliceNode.description, hres, hfeatures]

/-- Semantic current-form Theorem 4.1: ALICE's search tree contains the branch and description
generated by any incremental `b`-compression scheme, and the associated `D_s` reconstructs `x`
through the fixed Section 3.5 interpreter. -/
theorem theorem41_semantic
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    ∃ node, IsAliceBranch x node ∧ node.features = fs ∧
      node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x := by
  obtain ⟨node, hnode, hres, hfeatures⟩ :=
    exists_aliceBranch_of_incrementalBCompressionScheme hchain
  refine ⟨node, hnode, hfeatures, ?_, ?_⟩
  · simp [AliceNode.description, hres, hfeatures]
  · simpa [AliceNode.description, hres, hfeatures] using
      schemeDescriptionInterpreter_runs_of_incrementalBCompressionScheme hchain

/-- Uniform length bound for any autoencoder payload `g' f` appearing in an incremental
`b`-compression scheme. This is the Section 4 constant obtained by combining the bounded feature
length from Theorem 3.7 with the bounded descriptive-map length from Theorem 3.8. -/
def autoencoderPayloadBound (b : Nat) : Nat :=
  shortFeatureResidualMapBound (bCompressibleFeatureBound b) +
    bCompressibleFeatureBound b +
    (2 * BitString.blen
      (BitString.ofNat (shortFeatureResidualMapBound (bCompressibleFeatureBound b))) + 1)

theorem autoencoderPayload_length_le_of_bCompressionSchemeStep
    {b : Nat} {x f g r : Program}
    (hb : 1 < b)
    (hbc : BCompressible b x)
    (hstep : BCompressionSchemeStep b x f g r) :
    BitString.blen (autoencoderPayload g f) ≤ autoencoderPayloadBound b := by
  have hf :
      BitString.blen f ≤ bCompressibleFeatureBound b := by
    exact theorem37_shortestBFeature hb hbc hstep.shortestFeature
  have hg :
      BitString.blen g ≤ shortFeatureResidualMapBound (bCompressibleFeatureBound b) := by
    exact shortestDescriptiveMap_length_le_of_feature_length_le hstep.shortestMap hf
  have henc :
      BitString.blen (BitString.ofNatExact (BitString.blen g)) ≤
        BitString.blen (BitString.ofNat
          (shortFeatureResidualMapBound (bCompressibleFeatureBound b))) := by
    exact le_trans
      (BitString.blen_ofNatExact_le_ofNat (BitString.blen g))
      (BitString.blen_ofNat_mono hg)
  rw [autoencoderPayload, BitString.blen_exactPairPayload]
  unfold autoencoderPayloadBound
  omega

theorem autoencoderPayloads_bounded_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    List.Forall₂
      (fun f g => BitString.blen (autoencoderPayload g f) ≤ autoencoderPayloadBound b)
      fs gs := by
  induction hchain with
  | stop_small =>
      simp
  | stop_incompressible =>
      simp
  | @cons x f g r rs fs gs hbig hbc hstep hrest ih =>
      exact List.Forall₂.cons
        (autoencoderPayload_length_le_of_bCompressionSchemeStep hb hbc hstep)
        ih

/-- Nested runtime recurrence obtained by applying Lemma 4.1 step-by-step to a branch with
possibly varying payload lengths. The list `localWork` represents the non-recursive work done at
each node, such as computing `g_i` and `f_i` on that step. -/
def branchSearchTimeBound : List Program → List Program → List Nat → Nat
  | [], [], [] => 0
  | f :: fs, g :: gs, t :: ts =>
      2 ^ (BitString.blen (autoencoderPayload g f) + 1) *
        (t + branchSearchTimeBound fs gs ts + 1)
  | _, _, _ => 0

/-- Uniformized version of `branchSearchTimeBound` where every step uses the same payload-length
bound `payloadBound`. -/
def uniformBranchSearchTimeBound (payloadBound : Nat) : List Nat → Nat
  | [] => 0
  | t :: ts =>
      2 ^ (payloadBound + 1) * (t + uniformBranchSearchTimeBound payloadBound ts + 1)

theorem branchSearchTimeBound_le_uniform
    {payloadBound : Nat} {fs gs : List Program} {localWork : List Nat}
    (hpayload :
      List.Forall₂
        (fun f g => BitString.blen (autoencoderPayload g f) ≤ payloadBound)
        fs gs)
    (hlen : fs.length = localWork.length) :
    branchSearchTimeBound fs gs localWork ≤
      uniformBranchSearchTimeBound payloadBound localWork := by
  induction hpayload generalizing localWork with
  | nil =>
      cases localWork with
      | nil =>
          simp [branchSearchTimeBound, uniformBranchSearchTimeBound]
      | cons t ts =>
          simp at hlen
  | @cons f g fs gs hfg hrest ih =>
      cases localWork with
      | nil =>
          simp at hlen
      | cons t ts =>
          have hrestLen : fs.length = ts.length := by
            simpa using Nat.succ.inj hlen
          have hrestBound := ih hrestLen
          have hinner :
              t + branchSearchTimeBound fs gs ts + 1 ≤
                t + uniformBranchSearchTimeBound payloadBound ts + 1 := by
            omega
          have hpow :
              2 ^ (BitString.blen (autoencoderPayload g f) + 1) ≤
                2 ^ (payloadBound + 1) := by
            exact Nat.pow_le_pow_right (by decide) (by omega)
          calc
            branchSearchTimeBound (f :: fs) (g :: gs) (t :: ts) =
                2 ^ (BitString.blen (autoencoderPayload g f) + 1) *
                  (t + branchSearchTimeBound fs gs ts + 1) := by
              simp [branchSearchTimeBound]
            _ ≤ 2 ^ (BitString.blen (autoencoderPayload g f) + 1) *
                  (t + uniformBranchSearchTimeBound payloadBound ts + 1) := by
              exact Nat.mul_le_mul_left _ hinner
            _ ≤ 2 ^ (payloadBound + 1) *
                  (t + uniformBranchSearchTimeBound payloadBound ts + 1) := by
              simpa [Nat.mul_comm] using
                (Nat.mul_le_mul_right
                  (t + uniformBranchSearchTimeBound payloadBound ts + 1) hpow)
            _ = uniformBranchSearchTimeBound payloadBound (t :: ts) := by
              simp [uniformBranchSearchTimeBound]

/-- Current-form runtime reduction for Theorem 4.1: after collapsing all branch payload lengths
to the constant `autoencoderPayloadBound b`, the search cost of any incremental `b`-compression
scheme is bounded by a uniform Lemma 4.1 recurrence on the supplied local step costs. -/
theorem theorem41_runtimeReduction
    {b : Nat} {x rs : Program} {fs gs : List Program} {localWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hlen : fs.length = localWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      branchSearchTimeBound fs gs localWork ≤
        uniformBranchSearchTimeBound (autoencoderPayloadBound b) localWork := by
  obtain ⟨node, hnode, hfeatures, hdesc, hruns⟩ := theorem41_semantic hchain
  refine ⟨node, hnode, hdesc, hruns, ?_⟩
  exact branchSearchTimeBound_le_uniform
    (autoencoderPayloads_bounded_of_incrementalBCompressionScheme hb hchain)
    hlen

end

end Compression

end IcTheory
