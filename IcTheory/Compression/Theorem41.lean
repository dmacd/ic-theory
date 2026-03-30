import IcTheory.Compression.Section4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open scoped BigOperators

noncomputable section

/-- Total search budget allocated in phase `i` by the current concrete Section 4 schedule. -/
def phaseTotalBudget (i : Nat) : Nat :=
  ((phasePrograms i).map (phaseBudget i)).sum

/-- Total search budget consumed by the concrete Section 4 scheduler up to and including
phase `i`. This is the paper's total ALICE time parameter `T`. -/
def totalBudgetUntil : Nat → Nat
  | 0 => phaseTotalBudget 0
  | i + 1 => totalBudgetUntil i + phaseTotalBudget (i + 1)

private theorem decodePairPayload_pair_append (x y z : Program) :
    decodePairPayload (BitString.pair x y ++ z) = (x, y ++ z) := by
  simpa [BitString.pair, List.append_assoc] using
    (decodePairPayload_pair x (y ++ z))

private theorem autoencoderPayload_prefix_eq
    {g₁ f₁ g₂ f₂ : Program}
    (h : autoencoderPayload g₁ f₁ <+: autoencoderPayload g₂ f₂) :
    g₁ = g₂ ∧ f₁ = f₂ := by
  let t := (autoencoderPayload g₂ f₂).drop (BitString.blen (autoencoderPayload g₁ f₁))
  have ht : autoencoderPayload g₂ f₂ = autoencoderPayload g₁ f₁ ++ t := by
    exact List.prefix_append_drop h
  have hdecode :
      decodePairPayload (autoencoderPayload g₂ f₂) =
        decodePairPayload (autoencoderPayload g₁ f₁ ++ t) := by
    simpa [ht]
  have hpair :
      (g₂, BitString.e2 f₂) = (g₁, BitString.e2 f₁ ++ t) := by
    simpa [autoencoderPayload, decodePairPayload_pair_append] using hdecode
  have hg : g₂ = g₁ := congrArg Prod.fst hpair
  have he2 : BitString.e2 f₂ = BitString.e2 f₁ ++ t := congrArg Prod.snd hpair
  have hdecode₂ :
      decodePairPayload (BitString.e2 f₂) =
        decodePairPayload (BitString.e2 f₁ ++ t) := by
    exact congrArg decodePairPayload he2
  have hdecode₂' :
      decodePairPayload (BitString.pair (BitString.ofNat (BitString.blen f₂)) f₂) =
        decodePairPayload (BitString.pair (BitString.ofNat (BitString.blen f₁)) f₁ ++ t) := by
    simpa [BitString.e2, BitString.pair, List.append_assoc] using hdecode₂
  have hpair₂ :
      (BitString.ofNat (BitString.blen f₂), f₂) =
        (BitString.ofNat (BitString.blen f₁), f₁ ++ t) := by
    simpa [decodePairPayload_pair_append] using hdecode₂'
  have hlen : BitString.blen f₂ = BitString.blen f₁ := by
    simpa [BitString.ofNat] using congrArg Computability.decodeNat (congrArg Prod.fst hpair₂)
  have htNil : t = [] := by
    have := congrArg BitString.blen (congrArg Prod.snd hpair₂)
    simp [hlen] at this
    exact this
  have hf : f₂ = f₁ := by simpa [htNil] using (congrArg Prod.snd hpair₂)
  exact ⟨hg.symm, hf.symm⟩

private theorem isAutoencoderPayload_prefix_eq {a₁ a₂ : Program}
    (ha₁ : IsAutoencoderPayload a₁)
    (ha₂ : IsAutoencoderPayload a₂)
    (h : a₁ <+: a₂) :
    a₁ = a₂ := by
  rcases isAutoencoderPayload_iff_exists.mp ha₁ with ⟨g₁, f₁, rfl⟩
  rcases isAutoencoderPayload_iff_exists.mp ha₂ with ⟨g₂, f₂, rfl⟩
  exact autoencoderPayload_eq_iff.mpr (autoencoderPayload_prefix_eq h)

theorem nodup_phasePrograms (i : Nat) :
    (phasePrograms i).Nodup := by
  unfold phasePrograms
  exact (BitString.nodup_allUpToLength i).filter _

private def phaseProgramFinset (i : Nat) : Finset Program :=
  ⟨phasePrograms i, nodup_phasePrograms i⟩

private def phaseExtensionFinset (i : Nat) : Finset (Sigma fun _ : Program => Program) :=
  (phaseProgramFinset i).sigma fun a =>
    ⟨BitString.allOfLength (i - BitString.blen a), BitString.nodup_allOfLength _⟩

private theorem phaseTotalBudget_eq_finset_sum (i : Nat) :
    phaseTotalBudget i = Finset.sum (phaseProgramFinset i) (fun a => phaseBudget i a) := by
  rfl

private theorem card_phaseExtensionFinset (i : Nat) :
    (phaseExtensionFinset i).card = phaseTotalBudget i := by
  calc
    (phaseExtensionFinset i).card =
        Finset.sum (phaseProgramFinset i)
          (fun a => (BitString.allOfLength (i - BitString.blen a)).length) := by
      simpa [phaseExtensionFinset] using
        (Finset.card_sigma (phaseProgramFinset i)
          (fun a => ⟨BitString.allOfLength (i - BitString.blen a), BitString.nodup_allOfLength _⟩))
    _ = Finset.sum (phaseProgramFinset i) (fun a => phaseBudget i a) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simp [phaseProgramFinset] at ha
      simp [phaseBudget_eq_pow_of_mem_phasePrograms, ha]
    _ = phaseTotalBudget i := (phaseTotalBudget_eq_finset_sum i).symm

private def phaseExtensionWord : (Sigma fun _ : Program => Program) → Program
  | ⟨a, s⟩ => a ++ s

private theorem phaseExtensionWord_injOn (i : Nat) :
    Set.InjOn phaseExtensionWord (phaseExtensionFinset i) := by
  intro x hx y hy hxy
  rcases x with ⟨a₁, s₁⟩
  rcases y with ⟨a₂, s₂⟩
  simp [phaseExtensionFinset, phaseProgramFinset] at hx hy
  have ha₁ : IsAutoencoderPayload a₁ := hx.1.1
  have ha₂ : IsAutoencoderPayload a₂ := hy.1.1
  have hxy' : a₁ ++ s₁ = a₂ ++ s₂ := by
    simpa [phaseExtensionWord] using hxy
  have haEq : a₁ = a₂ := by
    by_cases hle : BitString.blen a₁ ≤ BitString.blen a₂
    · have hprefLong : a₁ <+: a₂ ++ s₂ := by
        exact ⟨s₁, hxy'⟩
      have hpref : a₁ <+: a₂ := (List.isPrefix_append_of_length hle).mp hprefLong
      exact isAutoencoderPayload_prefix_eq ha₁ ha₂ hpref
    · have hle' : BitString.blen a₂ ≤ BitString.blen a₁ := by omega
      have hprefLong : a₂ <+: a₁ ++ s₁ := by
        exact ⟨s₂, hxy'.symm⟩
      have hpref : a₂ <+: a₁ := (List.isPrefix_append_of_length hle').mp hprefLong
      exact (isAutoencoderPayload_prefix_eq ha₂ ha₁ hpref).symm
  have hsEq : s₁ = s₂ := by
    have hxy'' : a₁ ++ s₁ = a₁ ++ s₂ := by
      simpa [phaseExtensionWord, haEq] using hxy
    exact List.append_cancel_left hxy''
  subst haEq hsEq
  rfl

private theorem phaseExtensionWord_mem_allOfLength
    {i : Nat} {x : Sigma fun _ : Program => Program}
    (hx : x ∈ phaseExtensionFinset i) :
    phaseExtensionWord x ∈ BitString.allOfLength i := by
  rcases x with ⟨a, s⟩
  simp [phaseExtensionFinset, phaseProgramFinset] at hx
  have ha : BitString.blen a ≤ i := hx.1.2
  have hs : BitString.blen s = i - BitString.blen a := hx.2
  rw [BitString.mem_allOfLength_iff]
  have hlen : BitString.blen a + BitString.blen s = i := by
    rw [hs]
    omega
  simpa [phaseExtensionWord, BitString.blen_append] using hlen

theorem phaseTotalBudget_le_pow (i : Nat) :
    phaseTotalBudget i ≤ 2 ^ i := by
  let target : Finset Program := ⟨BitString.allOfLength i, BitString.nodup_allOfLength i⟩
  have hcard :
      phaseTotalBudget i = (phaseExtensionFinset i).card := by
    simpa using (card_phaseExtensionFinset i).symm
  have himage :
      (phaseExtensionFinset i).image phaseExtensionWord ⊆ target := by
    rw [Finset.image_subset_iff]
    intro x hx
    exact phaseExtensionWord_mem_allOfLength hx
  calc
    phaseTotalBudget i = ((phaseExtensionFinset i).image phaseExtensionWord).card := by
      rw [hcard]
      symm
      exact Finset.card_image_of_injOn (phaseExtensionWord_injOn i)
    _ ≤ target.card := Finset.card_le_card himage
    _ = 2 ^ i := by simp [target]

/-- Shortest codeword in the concrete Section 4 autoencoder prefix code. -/
def shortestAutoencoderPayloadLength : Nat :=
  BitString.blen (autoencoderPayload [] [])

private theorem shortestAutoencoderPayloadLength_le_of_isAutoencoderPayload {a : Program}
    (ha : IsAutoencoderPayload a) :
    shortestAutoencoderPayloadLength ≤ BitString.blen a := by
  rcases isAutoencoderPayload_iff_exists.mp ha with ⟨g, f, rfl⟩
  unfold shortestAutoencoderPayloadLength autoencoderPayload
  simp [BitString.blen_pair, BitString.blen_e2]
  omega

private theorem shortestAutoencoderPayload_mem_phasePrograms {i : Nat}
    (h : shortestAutoencoderPayloadLength ≤ i) :
    autoencoderPayload [] [] ∈ phasePrograms i := by
  rw [mem_phasePrograms_iff]
  exact ⟨isAutoencoderPayload_autoencoderPayload [] [], by simpa [shortestAutoencoderPayloadLength] using h⟩

theorem phaseTotalBudget_ge_shortestPayload {i : Nat}
    (h : shortestAutoencoderPayloadLength ≤ i) :
    2 ^ (i - shortestAutoencoderPayloadLength) ≤ phaseTotalBudget i := by
  have hmem : autoencoderPayload [] [] ∈ phaseProgramFinset i := by
    simpa [phaseProgramFinset] using shortestAutoencoderPayload_mem_phasePrograms h
  have hsingle :
      phaseBudget i (autoencoderPayload [] []) ≤
        Finset.sum (phaseProgramFinset i) (fun a => phaseBudget i a) := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  calc
    2 ^ (i - shortestAutoencoderPayloadLength) =
        phaseBudget i (autoencoderPayload [] []) := by
      symm
      simpa [shortestAutoencoderPayloadLength] using
        phaseBudget_eq_pow_of_mem_phasePrograms
          (shortestAutoencoderPayload_mem_phasePrograms h)
    _ ≤ Finset.sum (phaseProgramFinset i) (fun a => phaseBudget i a) := hsingle
    _ = phaseTotalBudget i := (phaseTotalBudget_eq_finset_sum i).symm

theorem phaseTotalBudget_le_totalBudgetUntil (i : Nat) :
    phaseTotalBudget i ≤ totalBudgetUntil i := by
  induction i with
  | zero =>
      simp [totalBudgetUntil]
  | succ i ih =>
      simpa [totalBudgetUntil, Nat.add_comm] using
        (Nat.le_add_left (phaseTotalBudget (i + 1)) (totalBudgetUntil i))

theorem totalBudgetUntil_le_pow_succ : ∀ i : Nat, totalBudgetUntil i ≤ 2 ^ (i + 1)
  | 0 => by
      exact le_trans (by simpa [totalBudgetUntil] using phaseTotalBudget_le_pow 0) (by decide)
  | i + 1 => by
      have ih := totalBudgetUntil_le_pow_succ i
      have hphase := phaseTotalBudget_le_pow (i + 1)
      calc
        totalBudgetUntil (i + 1) = totalBudgetUntil i + phaseTotalBudget (i + 1) := by
          simp [totalBudgetUntil]
        _ ≤ 2 ^ (i + 1) + 2 ^ (i + 1) := Nat.add_le_add ih hphase
        _ = 2 * 2 ^ (i + 1) := by rw [← two_mul]
        _ = 2 ^ (i + 2) := by
          calc
            2 * 2 ^ (i + 1) = (2 ^ i * 2) * 2 := by
              rw [Nat.pow_succ]
              ac_rfl
            _ = 2 ^ (i + 2) := by
              have hsucc : i + 2 = (i + 1) + 1 := by omega
              rw [hsucc, Nat.pow_succ, Nat.pow_succ]

theorem totalBudgetUntil_ge_pow_of_shortestPayload {i : Nat}
    (h : shortestAutoencoderPayloadLength ≤ i) :
    2 ^ (i - shortestAutoencoderPayloadLength) ≤ totalBudgetUntil i := by
  exact le_trans
    (phaseTotalBudget_ge_shortestPayload h)
    (phaseTotalBudget_le_totalBudgetUntil i)

/-- Total search budget allocated to a fixed node up to and including phase `i`. -/
def nodeBudgetUntil (a : Program) : Nat → Nat
  | 0 => phaseBudget 0 a
  | i + 1 => nodeBudgetUntil a i + phaseBudget (i + 1) a

theorem isAutoencoderPayload_length_pos {a : Program}
    (ha : IsAutoencoderPayload a) :
    0 < BitString.blen a := by
  rcases isAutoencoderPayload_iff_exists.mp ha with ⟨g, f, rfl⟩
  simp [autoencoderPayload, BitString.blen_pair, BitString.blen_e2]

private theorem phaseBudget_eq_zero_of_lt_length {a : Program} {i : Nat}
    (h : i < BitString.blen a) :
    phaseBudget i a = 0 := by
  by_cases ha : IsAutoencoderPayload a
  · simp [phaseBudget, ha, not_le.mpr h]
  · simp [phaseBudget, ha]

private theorem phaseBudget_eq_pow_of_length_le {a : Program} {i : Nat}
    (ha : IsAutoencoderPayload a)
    (h : BitString.blen a ≤ i) :
    phaseBudget i a = 2 ^ (i - BitString.blen a) := by
  simp [phaseBudget, ha, h]

@[simp] theorem nodeBudgetUntil_zero (a : Program) :
    nodeBudgetUntil a 0 = 0 := by
  by_cases ha : IsAutoencoderPayload a
  · have hpos : 0 < BitString.blen a := isAutoencoderPayload_length_pos ha
    simp [nodeBudgetUntil, phaseBudget, ha, not_le.mpr hpos]
  · simp [nodeBudgetUntil, phaseBudget, ha]

theorem nodeBudgetUntil_eq_zero_of_not_payload {a : Program}
    (ha : ¬ IsAutoencoderPayload a) :
    ∀ i : Nat, nodeBudgetUntil a i = 0
  | 0 => by simp [nodeBudgetUntil, phaseBudget, ha]
  | i + 1 => by
      simp [nodeBudgetUntil, nodeBudgetUntil_eq_zero_of_not_payload ha i, phaseBudget, ha]

theorem nodeBudgetUntil_eq_zero_of_lt_length {a : Program} {i : Nat}
    (h : i < BitString.blen a) :
    nodeBudgetUntil a i = 0 := by
  induction i with
  | zero =>
      exact nodeBudgetUntil_zero a
  | succ i ih =>
      rw [nodeBudgetUntil, ih (by omega), phaseBudget_eq_zero_of_lt_length h]

theorem nodeBudgetUntil_eq_closed_of_payload {a : Program}
    (ha : IsAutoencoderPayload a) (i : Nat) :
    nodeBudgetUntil a i =
      if i < BitString.blen a then 0 else 2 ^ (i - BitString.blen a + 1) - 1 := by
  induction i with
  | zero =>
      have hpos : 0 < BitString.blen a := isAutoencoderPayload_length_pos ha
      simp [nodeBudgetUntil, phaseBudget, ha, hpos, not_le.mpr hpos]
  | succ i ih =>
      by_cases hcur : i + 1 < BitString.blen a
      · have hprev : i < BitString.blen a := by omega
        rw [nodeBudgetUntil, ih, if_pos hprev, phaseBudget_eq_zero_of_lt_length hcur]
        simp [hcur]
      · have hle : BitString.blen a ≤ i + 1 := by omega
        by_cases hprev : i < BitString.blen a
        · have heq : i + 1 = BitString.blen a := by omega
          rw [nodeBudgetUntil, ih, if_pos hprev, phaseBudget_eq_pow_of_length_le ha hle]
          simp [hcur, heq]
        · have hlePrev : BitString.blen a ≤ i := by omega
          rw [nodeBudgetUntil, ih, if_neg hprev, phaseBudget_eq_pow_of_length_le ha hle]
          have hexp : i + 1 - BitString.blen a = i - BitString.blen a + 1 := by omega
          rw [if_neg hcur]
          rw [hexp]
          have hexp' :
              i - BitString.blen a + 1 + 1 = (i - BitString.blen a + 1) + 1 := by omega
          rw [hexp', Nat.pow_succ]
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

theorem nodeBudgetWitness_payload {a : Program} {τ n : Nat}
    (hw : NodeBudgetWitness a τ n) :
    IsAutoencoderPayload a := by
  by_contra ha
  have hzero : nodeBudgetUntil a (n + 1) = 0 :=
    nodeBudgetUntil_eq_zero_of_not_payload ha (n + 1)
  have hτ0 : τ = 0 := by
    apply le_antisymm
    · simpa [hzero] using hw.2
    · exact Nat.zero_le _
  exact (Nat.ne_of_gt (nodeBudgetWitness_pos hw)) hτ0

theorem length_le_succ_of_nodeBudgetWitness {a : Program} {τ n : Nat}
    (hw : NodeBudgetWitness a τ n) :
    BitString.blen a ≤ n + 1 := by
  have ha : IsAutoencoderPayload a := nodeBudgetWitness_payload hw
  by_contra hlen
  have hzero : nodeBudgetUntil a (n + 1) = 0 :=
    nodeBudgetUntil_eq_zero_of_lt_length (a := a) (i := n + 1) (by omega)
  have hτ0 : τ = 0 := by
    apply le_antisymm
    · simpa [hzero] using hw.2
    · exact Nat.zero_le _
  exact (Nat.ne_of_gt (nodeBudgetWitness_pos hw)) hτ0

theorem nodeBudgetWitness_pow_le {a : Program} {τ n : Nat}
    (hw : NodeBudgetWitness a τ n) :
    2 ^ (n + 1 - BitString.blen a) ≤ τ := by
  have ha : IsAutoencoderPayload a := nodeBudgetWitness_payload hw
  have hlen : BitString.blen a ≤ n + 1 := length_le_succ_of_nodeBudgetWitness hw
  by_cases hprev : n < BitString.blen a
  · have heq : n + 1 = BitString.blen a := by omega
    have hzero : nodeBudgetUntil a n = 0 :=
      nodeBudgetUntil_eq_zero_of_lt_length (a := a) (i := n) hprev
    have hτ : 0 < τ := by simpa [hzero] using hw.1
    simpa [heq] using Nat.succ_le_of_lt hτ
  · have hclosed :
        nodeBudgetUntil a n = 2 ^ (n - BitString.blen a + 1) - 1 := by
      simpa [if_neg hprev] using nodeBudgetUntil_eq_closed_of_payload ha n
    have hlt : 2 ^ (n - BitString.blen a + 1) - 1 < τ := by
      simpa [hclosed] using hw.1
    have hexp : n + 1 - BitString.blen a = n - BitString.blen a + 1 := by omega
    rw [hexp]
    omega

/-- Abstract upper half of the paper's Lemma 4.1 under the prefix-style phase-mass model. -/
theorem lemma41_upper_of_prefixPhaseModel
    {total : Nat → Nat} {amin : Nat} {a : Program} {τ n : Nat}
    (hmodel : PrefixPhaseModel total amin)
    (hw : NodeBudgetWitness a τ n) :
    total (n + 1) ≤ 2 ^ (BitString.blen a + 1) * τ := by
  have hupper := hmodel.upper (n + 1)
  have hlen : BitString.blen a ≤ n + 1 := length_le_succ_of_nodeBudgetWitness hw
  have hpow : 2 ^ (n + 1 - BitString.blen a) ≤ τ :=
    nodeBudgetWitness_pow_le hw
  calc
    total (n + 1) ≤ 2 ^ (n + 2) := by
      simpa using hupper
    _ = 2 ^ (BitString.blen a + 1) * 2 ^ (n + 1 - BitString.blen a) := by
      have hexp : n + 2 = BitString.blen a + 1 + (n + 1 - BitString.blen a) := by
        omega
      rw [hexp, Nat.pow_add]
    _ ≤ 2 ^ (BitString.blen a + 1) * τ := by
      exact Nat.mul_le_mul_left _ hpow

/-- Abstract lower half of the paper's Lemma 4.1 with the fractional `2^{-1}` factor cleared:
`2^(|a|-|amin|) * τ < 2 * T`. -/
theorem lemma41_lower_of_prefixPhaseModel
    {total : Nat → Nat} {amin : Nat} {a : Program} {τ n : Nat}
    (hmodel : PrefixPhaseModel total amin)
    (hmin : amin ≤ BitString.blen a)
    (hw : NodeBudgetWitness a τ n) :
    2 ^ (BitString.blen a - amin) * τ < 2 * total (n + 1) := by
  have ha : IsAutoencoderPayload a := nodeBudgetWitness_payload hw
  have hnode :
      nodeBudgetUntil a (n + 1) =
        if n + 1 < BitString.blen a then 0 else 2 ^ (n + 1 - BitString.blen a + 1) - 1 :=
    nodeBudgetUntil_eq_closed_of_payload ha (n + 1)
  have hlen : BitString.blen a ≤ n + 1 := length_le_succ_of_nodeBudgetWitness hw
  have hτpow : τ < 2 ^ (n + 1 - BitString.blen a + 1) := by
    rw [if_neg (by omega)] at hnode
    have hwNext : τ ≤ 2 ^ (n + 1 - BitString.blen a + 1) - 1 := by
      simpa [hnode] using hw.2
    exact lt_of_le_of_lt hwNext (Nat.sub_lt (pow_pos (show 0 < 2 by decide) _) (by decide))
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

/-- Packaged paper-form Lemma 4.1 under the abstract prefix-style phase model. -/
theorem lemma41_of_prefixPhaseModel
    {total : Nat → Nat} {amin : Nat} {a : Program} {τ n : Nat}
    (hmodel : PrefixPhaseModel total amin)
    (hmin : amin ≤ BitString.blen a)
    (hw : NodeBudgetWitness a τ n) :
    total (n + 1) ≤ 2 ^ (BitString.blen a + 1) * τ ∧
      2 ^ (BitString.blen a - amin) * τ < 2 * total (n + 1) := by
  exact ⟨
    lemma41_upper_of_prefixPhaseModel hmodel hw,
    lemma41_lower_of_prefixPhaseModel hmodel hmin hw
  ⟩

/-- The concrete Section 4 scheduler satisfies the paper's prefix-style phase-mass model with the
shortest valid autoencoder payload as its minimal codeword. -/
theorem totalBudgetUntil_prefixPhaseModel :
    PrefixPhaseModel totalBudgetUntil shortestAutoencoderPayloadLength := by
  refine ⟨totalBudgetUntil_le_pow_succ, ?_⟩
  intro n hn
  exact totalBudgetUntil_ge_pow_of_shortestPayload hn

/-- Concrete paper-form Lemma 4.1 for the live Section 4 scheduler. If phase `n + 1` is the
first phase by which node `a` has received at least `τ` steps, then the total ALICE time through
that phase lies between the paper's lower and upper bounds. -/
theorem lemma41
    {a : Program} {τ n : Nat}
    (hw : NodeBudgetWitness a τ n) :
    totalBudgetUntil (n + 1) ≤ 2 ^ (BitString.blen a + 1) * τ ∧
      2 ^ (BitString.blen a - shortestAutoencoderPayloadLength) * τ <
        2 * totalBudgetUntil (n + 1) := by
  have ha : IsAutoencoderPayload a := nodeBudgetWitness_payload hw
  have hmin : shortestAutoencoderPayloadLength ≤ BitString.blen a :=
    shortestAutoencoderPayloadLength_le_of_isAutoencoderPayload ha
  simpa using
    lemma41_of_prefixPhaseModel
      (total := totalBudgetUntil)
      (amin := shortestAutoencoderPayloadLength)
      totalBudgetUntil_prefixPhaseModel
      hmin hw

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
  2 * shortFeatureResidualMapBound (bCompressibleFeatureBound b) +
    bCompressibleFeatureBound b +
    (2 * BitString.blen
      (BitString.ofNat (bCompressibleFeatureBound b)) + 2)

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
      BitString.blen (BitString.ofNat (BitString.blen f)) ≤
        BitString.blen (BitString.ofNat
          (bCompressibleFeatureBound b)) := by
    exact BitString.blen_ofNat_mono hf
  rw [autoencoderPayload, BitString.blen_pair, BitString.blen_e2]
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

private theorem sum_map_mul_left (a : Nat) (l : List Nat) :
    (l.map (fun n => a * n)).sum = a * l.sum := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp [Nat.left_distrib, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Explicit weighted terms whose sum equals the nested branch recurrence. -/
def branchSearchTimeTerms : List Program → List Program → List Nat → List Nat
  | [], [], [] => []
  | f :: fs, g :: gs, t :: ts =>
      let a := 2 ^ (BitString.blen (autoencoderPayload g f) + 1)
      let tail := branchSearchTimeTerms fs gs ts
      a * (t + 1) :: tail.map (fun n => a * n)
  | _, _, _ => []

/-- Uniform weighted terms for the constant-payload-length recurrence. -/
def uniformBranchSearchTimeTerms (payloadBound : Nat) : List Nat → List Nat
  | [] => []
  | t :: ts =>
      let a := 2 ^ (payloadBound + 1)
      let tail := uniformBranchSearchTimeTerms payloadBound ts
      a * (t + 1) :: tail.map (fun n => a * n)

/-- Exact per-step exponent contributed by one Section 4 autoencoder payload. This is the
current-model replacement for the paper term `l(f_i) + l(f_i') + O(1)`. -/
def autoencoderStepExponent (g f : Program) : Nat :=
  2 * BitString.blen g + BitString.blen f +
    (2 * BitString.blen (BitString.ofNat (BitString.blen f)) + 3)

@[simp] theorem autoencoderStepExponent_eq_payload (g f : Program) :
    autoencoderStepExponent g f = BitString.blen (autoencoderPayload g f) + 1 := by
  rw [autoencoderPayload, BitString.blen_pair, BitString.blen_e2]
  unfold autoencoderStepExponent
  omega

/-- One-step linear overhead witnessing the paper's `O(i)` exponent slack for Section 4 along a
`b`-compression branch. It depends only on the fixed `b` through the Section 3.4 constants for
short features and short descriptive maps. -/
def autoencoderPaperOverhead (b : Nat) : Nat :=
  shortFeatureResidualMapBound (bCompressibleFeatureBound b) +
    (2 * BitString.blen (BitString.ofNat (bCompressibleFeatureBound b)) + 3)

/-- Paper-facing one-step exponent `l(f_i) + l(f_i') + O(1)` used in Theorem 4.1. -/
def paperAutoencoderStepExponent (b : Nat) (g f : Program) : Nat :=
  BitString.blen g + BitString.blen f + autoencoderPaperOverhead b

private theorem autoencoderStepExponent_le_of_featureMapBounds
    {g f : Program} {featureBound mapBound : Nat}
    (hf : BitString.blen f ≤ featureBound)
    (hg : BitString.blen g ≤ mapBound) :
    autoencoderStepExponent g f ≤
      BitString.blen f + BitString.blen g +
        (mapBound + (2 * BitString.blen (BitString.ofNat featureBound) + 3)) := by
  have henc :
      BitString.blen (BitString.ofNat (BitString.blen f)) ≤
        BitString.blen (BitString.ofNat featureBound) := by
    exact BitString.blen_ofNat_mono hf
  unfold autoencoderStepExponent
  omega

theorem autoencoderStepExponent_le_paper_of_bCompressionSchemeStep
    {b : Nat} {x f g r : Program}
    (hb : 1 < b)
    (hbc : BCompressible b x)
    (hstep : BCompressionSchemeStep b x f g r) :
    autoencoderStepExponent g f ≤ paperAutoencoderStepExponent b g f := by
  have hf :
      BitString.blen f ≤ bCompressibleFeatureBound b := by
    exact theorem37_shortestBFeature hb hbc hstep.shortestFeature
  have hg :
      BitString.blen g ≤ shortFeatureResidualMapBound (bCompressibleFeatureBound b) := by
    exact shortestDescriptiveMap_length_le_of_feature_length_le hstep.shortestMap hf
  simpa [paperAutoencoderStepExponent, autoencoderPaperOverhead,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    autoencoderStepExponent_le_of_featureMapBounds hf hg

/-- Cumulative payload exponents along a branch. The `i`-th entry is the sum of the current-model
payload exponents through step `i`. -/
def branchSearchTimeExponents : List Program → List Program → List Nat
  | [], [] => []
  | f :: fs, g :: gs =>
      let a := autoencoderStepExponent g f
      let tail := branchSearchTimeExponents fs gs
      a :: tail.map (fun n => a + n)
  | _, _ => []

/-- Exact weighted local terms attached to `branchSearchTimeBound`. This makes the cumulative
payload exponents explicit, giving the current-form analogue of the paper's weighted sum. -/
def branchSearchTimeExplicitTerms (fs gs : List Program) (localWork : List Nat) : List Nat :=
  List.zipWith (fun t e => 2 ^ e * (t + 1)) localWork (branchSearchTimeExponents fs gs)

theorem branchSearchTimeBound_eq_sum_terms
    (fs gs : List Program) (localWork : List Nat) :
    branchSearchTimeBound fs gs localWork = (branchSearchTimeTerms fs gs localWork).sum := by
  induction fs generalizing gs localWork with
  | nil =>
      cases gs <;> cases localWork <;> simp [branchSearchTimeBound, branchSearchTimeTerms]
  | cons f fs ih =>
      cases gs with
      | nil =>
          cases localWork <;> simp [branchSearchTimeBound, branchSearchTimeTerms]
      | cons g gs =>
          cases localWork with
          | nil =>
              simp [branchSearchTimeBound, branchSearchTimeTerms]
          | cons t ts =>
              simp [branchSearchTimeBound, branchSearchTimeTerms]
              rw [sum_map_mul_left, ih]
              rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
              ac_rfl

theorem uniformBranchSearchTimeBound_eq_sum_terms
    (payloadBound : Nat) (localWork : List Nat) :
    uniformBranchSearchTimeBound payloadBound localWork =
      (uniformBranchSearchTimeTerms payloadBound localWork).sum := by
  induction localWork with
  | nil =>
      simp [uniformBranchSearchTimeBound, uniformBranchSearchTimeTerms]
  | cons t ts ih =>
      simp [uniformBranchSearchTimeBound, uniformBranchSearchTimeTerms]
      rw [sum_map_mul_left, ih]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
      ac_rfl

private theorem zipWith_pow_map_add
    (a : Nat) (ts exps : List Nat) :
    List.zipWith (fun t e => 2 ^ e * (t + 1)) ts (exps.map (fun n => a + n)) =
      (List.zipWith (fun t e => 2 ^ e * (t + 1)) ts exps).map (fun n => 2 ^ a * n) := by
  induction ts generalizing exps with
  | nil =>
      cases exps <;> simp
  | cons t ts ih =>
      cases exps with
      | nil =>
          simp
      | cons e exps =>
          simp [List.zipWith, ih]
          rw [Nat.pow_add]
          ac_rfl

theorem branchSearchTimeTerms_eq_explicitTerms
    (fs gs : List Program) (localWork : List Nat) :
    branchSearchTimeTerms fs gs localWork = branchSearchTimeExplicitTerms fs gs localWork := by
  induction fs generalizing gs localWork with
  | nil =>
      cases gs <;> cases localWork <;>
        simp [branchSearchTimeTerms, branchSearchTimeExplicitTerms, branchSearchTimeExponents]
  | cons f fs ih =>
      cases gs with
      | nil =>
          cases localWork <;>
            simp [branchSearchTimeTerms, branchSearchTimeExplicitTerms, branchSearchTimeExponents]
      | cons g gs =>
          cases localWork with
          | nil =>
              simp [branchSearchTimeTerms, branchSearchTimeExplicitTerms, branchSearchTimeExponents]
          | cons t ts =>
              simp [branchSearchTimeTerms, branchSearchTimeExplicitTerms, branchSearchTimeExponents,
                autoencoderStepExponent_eq_payload]
              rw [ih]
              have hzip :
                  List.map (fun n => 2 ^ (BitString.blen (autoencoderPayload g f) + 1) * n)
                      (branchSearchTimeExplicitTerms fs gs ts) =
                    List.zipWith (fun t e => 2 ^ e * (t + 1)) ts
                      (List.map (fun n => BitString.blen (autoencoderPayload g f) + 1 + n)
                        (branchSearchTimeExponents fs gs)) := by
                calc
                  List.map (fun n => 2 ^ (BitString.blen (autoencoderPayload g f) + 1) * n)
                      (branchSearchTimeExplicitTerms fs gs ts) =
                      List.map (fun n => 2 ^ (BitString.blen (autoencoderPayload g f) + 1) * n)
                        (List.zipWith (fun t e => 2 ^ e * (t + 1)) ts
                          (branchSearchTimeExponents fs gs)) := by
                    rfl
                  _ = List.zipWith (fun t e => 2 ^ e * (t + 1)) ts
                        (List.map (fun n => BitString.blen (autoencoderPayload g f) + 1 + n)
                          (branchSearchTimeExponents fs gs)) := by
                    simpa [autoencoderStepExponent_eq_payload] using
                      (zipWith_pow_map_add (a := autoencoderStepExponent g f)
                        (ts := ts) (exps := branchSearchTimeExponents fs gs)).symm
              exact hzip

theorem branchSearchTimeBound_eq_sum_explicitTerms
    (fs gs : List Program) (localWork : List Nat) :
    branchSearchTimeBound fs gs localWork = (branchSearchTimeExplicitTerms fs gs localWork).sum := by
  rw [branchSearchTimeBound_eq_sum_terms, branchSearchTimeTerms_eq_explicitTerms]

/-- Nested runtime recurrence in the paper's exponent shape
`Σ_{k≤i} (l(f_k) + l(f_k') + O(1))`. The fixed additive constant hidden in the `O(1)` is
`autoencoderPaperOverhead b`. -/
def branchSearchTimePaperBound (b : Nat) : List Program → List Program → List Nat → Nat
  | [], [], [] => 0
  | f :: fs, g :: gs, t :: ts =>
      2 ^ (paperAutoencoderStepExponent b g f) *
        (t + branchSearchTimePaperBound b fs gs ts + 1)
  | _, _, _ => 0

/-- Weighted terms whose sum equals `branchSearchTimePaperBound`. -/
def branchSearchTimePaperTerms (b : Nat) : List Program → List Program → List Nat → List Nat
  | [], [], [] => []
  | f :: fs, g :: gs, t :: ts =>
      let a := 2 ^ (paperAutoencoderStepExponent b g f)
      let tail := branchSearchTimePaperTerms b fs gs ts
      a * (t + 1) :: tail.map (fun n => a * n)
  | _, _, _ => []

/-- Cumulative paper-form exponents for Theorem 4.1. -/
def branchSearchTimePaperExponents (b : Nat) : List Program → List Program → List Nat
  | [], [] => []
  | f :: fs, g :: gs =>
      let a := paperAutoencoderStepExponent b g f
      let tail := branchSearchTimePaperExponents b fs gs
      a :: tail.map (fun n => a + n)
  | _, _ => []

/-- Explicit paper-form weighted terms for Theorem 4.1. The `i`-th exponent is the cumulative
sum of `l(f_k) + l(f_k') + autoencoderPaperOverhead b` through step `i`, i.e. the paper's
`Σ_{k≤i} (l(f_k) + l(f_k')) + O(i)` factor. -/
def branchSearchTimePaperExplicitTerms
    (b : Nat) (fs gs : List Program) (localWork : List Nat) : List Nat :=
  List.zipWith (fun t e => 2 ^ e * (t + 1)) localWork (branchSearchTimePaperExponents b fs gs)

theorem branchSearchTimePaperBound_eq_sum_terms
    (b : Nat) (fs gs : List Program) (localWork : List Nat) :
    branchSearchTimePaperBound b fs gs localWork =
      (branchSearchTimePaperTerms b fs gs localWork).sum := by
  induction fs generalizing gs localWork with
  | nil =>
      cases gs <;> cases localWork <;>
        simp [branchSearchTimePaperBound, branchSearchTimePaperTerms]
  | cons f fs ih =>
      cases gs with
      | nil =>
          cases localWork <;>
            simp [branchSearchTimePaperBound, branchSearchTimePaperTerms]
      | cons g gs =>
          cases localWork with
          | nil =>
              simp [branchSearchTimePaperBound, branchSearchTimePaperTerms]
          | cons t ts =>
              simp [branchSearchTimePaperBound, branchSearchTimePaperTerms]
              rw [sum_map_mul_left, ih]
              rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
              ac_rfl

theorem branchSearchTimePaperTerms_eq_explicitTerms
    (b : Nat) (fs gs : List Program) (localWork : List Nat) :
    branchSearchTimePaperTerms b fs gs localWork =
      branchSearchTimePaperExplicitTerms b fs gs localWork := by
  induction fs generalizing gs localWork with
  | nil =>
      cases gs <;> cases localWork <;>
        simp [branchSearchTimePaperTerms, branchSearchTimePaperExplicitTerms,
          branchSearchTimePaperExponents]
  | cons f fs ih =>
      cases gs with
      | nil =>
          cases localWork <;>
            simp [branchSearchTimePaperTerms, branchSearchTimePaperExplicitTerms,
              branchSearchTimePaperExponents]
      | cons g gs =>
          cases localWork with
          | nil =>
              simp [branchSearchTimePaperTerms, branchSearchTimePaperExplicitTerms,
                branchSearchTimePaperExponents]
          | cons t ts =>
              simp [branchSearchTimePaperTerms, branchSearchTimePaperExplicitTerms,
                branchSearchTimePaperExponents]
              rw [ih]
              have hzip :
                  List.map (fun n => 2 ^ (paperAutoencoderStepExponent b g f) * n)
                      (branchSearchTimePaperExplicitTerms b fs gs ts) =
                    List.zipWith (fun t e => 2 ^ e * (t + 1)) ts
                      (List.map (fun n => paperAutoencoderStepExponent b g f + n)
                        (branchSearchTimePaperExponents b fs gs)) := by
                calc
                  List.map (fun n => 2 ^ (paperAutoencoderStepExponent b g f) * n)
                      (branchSearchTimePaperExplicitTerms b fs gs ts) =
                      List.map (fun n => 2 ^ (paperAutoencoderStepExponent b g f) * n)
                        (List.zipWith (fun t e => 2 ^ e * (t + 1)) ts
                          (branchSearchTimePaperExponents b fs gs)) := by
                    rfl
                  _ = List.zipWith (fun t e => 2 ^ e * (t + 1)) ts
                        (List.map (fun n => paperAutoencoderStepExponent b g f + n)
                          (branchSearchTimePaperExponents b fs gs)) := by
                    simpa using
                      (zipWith_pow_map_add (a := paperAutoencoderStepExponent b g f)
                        (ts := ts) (exps := branchSearchTimePaperExponents b fs gs)).symm
              exact hzip

theorem branchSearchTimePaperBound_eq_sum_explicitTerms
    (b : Nat) (fs gs : List Program) (localWork : List Nat) :
    branchSearchTimePaperBound b fs gs localWork =
      (branchSearchTimePaperExplicitTerms b fs gs localWork).sum := by
  rw [branchSearchTimePaperBound_eq_sum_terms, branchSearchTimePaperTerms_eq_explicitTerms]

theorem incrementalBCompressionScheme_stepExponent_paperBound
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    List.Forall₂
      (fun f g => autoencoderStepExponent g f ≤ paperAutoencoderStepExponent b g f)
      fs gs := by
  induction hchain with
  | stop_small =>
      simp
  | stop_incompressible =>
      simp
  | @cons x f g r rs fs gs hbig hbc hstep hrest ih =>
      exact List.Forall₂.cons
        (autoencoderStepExponent_le_paper_of_bCompressionSchemeStep hb hbc hstep)
        ih

theorem branchSearchTimeBound_le_paper
    {b : Nat} {fs gs : List Program} {localWork : List Nat}
    (hsteps :
      List.Forall₂
        (fun f g => autoencoderStepExponent g f ≤ paperAutoencoderStepExponent b g f)
        fs gs)
    (hlen : fs.length = localWork.length) :
    branchSearchTimeBound fs gs localWork ≤ branchSearchTimePaperBound b fs gs localWork := by
  induction hsteps generalizing localWork with
  | nil =>
      cases localWork with
      | nil =>
          simp [branchSearchTimeBound, branchSearchTimePaperBound]
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
                t + branchSearchTimePaperBound b fs gs ts + 1 := by
            omega
          have hpow :
              2 ^ (autoencoderStepExponent g f) ≤
                2 ^ (paperAutoencoderStepExponent b g f) := by
            exact Nat.pow_le_pow_right (by decide) hfg
          calc
            branchSearchTimeBound (f :: fs) (g :: gs) (t :: ts) =
                2 ^ (autoencoderStepExponent g f) *
                  (t + branchSearchTimeBound fs gs ts + 1) := by
              simp [branchSearchTimeBound, autoencoderStepExponent_eq_payload]
            _ ≤ 2 ^ (autoencoderStepExponent g f) *
                  (t + branchSearchTimePaperBound b fs gs ts + 1) := by
              exact Nat.mul_le_mul_left _ hinner
            _ ≤ 2 ^ (paperAutoencoderStepExponent b g f) *
                  (t + branchSearchTimePaperBound b fs gs ts + 1) := by
              simpa [Nat.mul_comm] using
                (Nat.mul_le_mul_right
                  (t + branchSearchTimePaperBound b fs gs ts + 1) hpow)
            _ = branchSearchTimePaperBound b (f :: fs) (g :: gs) (t :: ts) := by
              simp [branchSearchTimePaperBound]

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

/-- Weighted-sum version of the current Theorem 4.1 runtime reduction. The nested branch
recurrence is rewritten as an explicit sum of weighted local step costs, and then compared against
the corresponding uniform weighted sum at payload bound `autoencoderPayloadBound b`. -/
theorem theorem41_runtimeReduction_weighted
    {b : Nat} {x rs : Program} {fs gs : List Program} {localWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hlen : fs.length = localWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      (branchSearchTimeTerms fs gs localWork).sum ≤
        (uniformBranchSearchTimeTerms (autoencoderPayloadBound b) localWork).sum := by
  obtain ⟨node, hnode, hdesc, hruns, hbound⟩ :=
    theorem41_runtimeReduction hb hchain hlen
  refine ⟨node, hnode, hdesc, hruns, ?_⟩
  rw [← branchSearchTimeBound_eq_sum_terms, ← uniformBranchSearchTimeBound_eq_sum_terms]
  exact hbound

/-- Paper-shape current-form runtime reduction for Theorem 4.1. The search time is written as an
explicit weighted sum whose `i`-th exponent is the cumulative payload cost
`∑_{k ≤ i} autoencoderStepExponent g_k f_k`, then compared to the uniform weighted bound. -/
theorem theorem41_runtimeReduction_explicit
    {b : Nat} {x rs : Program} {fs gs : List Program} {localWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hlen : fs.length = localWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      branchSearchTimeBound fs gs localWork =
        (branchSearchTimeExplicitTerms fs gs localWork).sum ∧
      (branchSearchTimeExplicitTerms fs gs localWork).sum ≤
        (uniformBranchSearchTimeTerms (autoencoderPayloadBound b) localWork).sum := by
  obtain ⟨node, hnode, hdesc, hruns, hbound⟩ :=
    theorem41_runtimeReduction_weighted hb hchain hlen
  refine ⟨node, hnode, hdesc, hruns, ?_, ?_⟩
  · exact branchSearchTimeBound_eq_sum_explicitTerms fs gs localWork
  · simpa [branchSearchTimeTerms_eq_explicitTerms] using hbound

/-- Paper-notation wrapper for `theorem41_runtimeReduction_explicit`. Here `featureWork`
corresponds to the time list `t_i` for computing `f_i (r_i)`, while `mapWork` corresponds to the
time list `t_i'` for computing `g_i (r_{i-1})`. The current-form weighted bound is then stated on
their pointwise sum. -/
theorem theorem41_runtimeReduction_explicit_split
    {b : Nat} {x rs : Program} {fs gs : List Program}
    {featureWork mapWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hfeatureLen : fs.length = featureWork.length)
    (hmapLen : gs.length = mapWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      branchSearchTimeBound fs gs (List.zipWith (· + ·) featureWork mapWork) =
        (branchSearchTimeExplicitTerms fs gs
          (List.zipWith (· + ·) featureWork mapWork)).sum ∧
      (branchSearchTimeExplicitTerms fs gs
          (List.zipWith (· + ·) featureWork mapWork)).sum ≤
        (uniformBranchSearchTimeTerms (autoencoderPayloadBound b)
          (List.zipWith (· + ·) featureWork mapWork)).sum := by
  let localWork := List.zipWith (· + ·) featureWork mapWork
  have hlen : fs.length = localWork.length := by
    have hwork : featureWork.length = mapWork.length := by
      calc
        featureWork.length = fs.length := by simpa using hfeatureLen.symm
        _ = gs.length := incrementalBCompressionScheme_lengths_eq hchain
        _ = mapWork.length := by simpa using hmapLen
    rw [List.length_zipWith, hfeatureLen]
    simpa [hwork]
  simpa [localWork] using theorem41_runtimeReduction_explicit hb hchain hlen

/-- Closed-form arithmetic upper bound for the uniform branch recurrence. This is a coarser but
fully explicit replacement for the nested search-time definition. -/
theorem uniformBranchSearchTimeBound_le_closed
    (payloadBound : Nat) (localWork : List Nat) :
    uniformBranchSearchTimeBound payloadBound localWork ≤
      (localWork.sum + localWork.length) *
        2 ^ ((payloadBound + 1) * localWork.length) := by
  induction localWork with
  | nil =>
      simp [uniformBranchSearchTimeBound]
  | cons t ts ih =>
      let a := 2 ^ (payloadBound + 1)
      let big := 2 ^ ((payloadBound + 1) * (ts.length + 1))
      have htail :
          a * uniformBranchSearchTimeBound payloadBound ts ≤
            (ts.sum + ts.length) * big := by
        calc
          a * uniformBranchSearchTimeBound payloadBound ts ≤
              a * ((ts.sum + ts.length) * 2 ^ ((payloadBound + 1) * ts.length)) := by
            exact Nat.mul_le_mul_left _ ih
          _ = (ts.sum + ts.length) * big := by
            dsimp [a, big]
            calc
              2 ^ (payloadBound + 1) * ((ts.sum + ts.length) * 2 ^ ((payloadBound + 1) * ts.length)) =
                  (ts.sum + ts.length) *
                    (2 ^ (payloadBound + 1) * 2 ^ ((payloadBound + 1) * ts.length)) := by
                ac_rfl
              _ = (ts.sum + ts.length) *
                  2 ^ ((payloadBound + 1) + (payloadBound + 1) * ts.length) := by
                rw [← Nat.pow_add]
            have hexp :
                (payloadBound + 1) + (payloadBound + 1) * ts.length =
                  (payloadBound + 1) * (ts.length + 1) := by
              rw [Nat.mul_add, Nat.mul_one]
              ac_rfl
            rw [hexp]
      have hpow :
          a ≤ big := by
        dsimp [a, big]
        refine Nat.pow_le_pow_right (by decide) ?_
        calc
          payloadBound + 1 = (payloadBound + 1) * 1 := by simp
          _ ≤ (payloadBound + 1) * (ts.length + 1) := by
            exact Nat.mul_le_mul_left _ (by simp)
      have hhead :
          a * (t + 1) ≤ (t + 1) * big := by
        calc
          a * (t + 1) = (t + 1) * a := by ac_rfl
          _ ≤ (t + 1) * big := by
            exact Nat.mul_le_mul_left _ hpow
      calc
        uniformBranchSearchTimeBound payloadBound (t :: ts) =
            a * uniformBranchSearchTimeBound payloadBound ts + a * (t + 1) := by
          dsimp [uniformBranchSearchTimeBound, a]
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
          ac_rfl
        _ ≤ (ts.sum + ts.length) * big + (t + 1) * big := by
          exact Nat.add_le_add htail hhead
        _ = ((t :: ts).sum + (t :: ts).length) * big := by
          simp [List.sum_cons, big, Nat.right_distrib, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

/-- Explicit current-form runtime bound for Theorem 4.1. It combines the semantic branch
extraction with the uniform payload bound and collapses the nested search-time recurrence into a
single arithmetic expression. -/
theorem theorem41_runtimeReduction_closed
    {b : Nat} {x rs : Program} {fs gs : List Program} {localWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hlen : fs.length = localWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      branchSearchTimeBound fs gs localWork ≤
        (localWork.sum + localWork.length) *
          2 ^ ((autoencoderPayloadBound b + 1) * localWork.length) := by
  obtain ⟨node, hnode, hdesc, hruns, hbound⟩ :=
    theorem41_runtimeReduction hb hchain hlen
  refine ⟨node, hnode, hdesc, hruns, ?_⟩
  exact le_trans hbound
    (uniformBranchSearchTimeBound_le_closed (autoencoderPayloadBound b) localWork)

/-- Closed-form split-work wrapper for Theorem 4.1, using separate `t_i` and `t_i'` lists. -/
theorem theorem41_runtimeReduction_closed_split
    {b : Nat} {x rs : Program} {fs gs : List Program}
    {featureWork mapWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hfeatureLen : fs.length = featureWork.length)
    (hmapLen : gs.length = mapWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      branchSearchTimeBound fs gs (List.zipWith (· + ·) featureWork mapWork) ≤
        ((List.zipWith (· + ·) featureWork mapWork).sum +
            (List.zipWith (· + ·) featureWork mapWork).length) *
          2 ^ ((autoencoderPayloadBound b + 1) *
            (List.zipWith (· + ·) featureWork mapWork).length) := by
  let localWork := List.zipWith (· + ·) featureWork mapWork
  have hlen : fs.length = localWork.length := by
    have hwork : featureWork.length = mapWork.length := by
      calc
        featureWork.length = fs.length := by simpa using hfeatureLen.symm
        _ = gs.length := incrementalBCompressionScheme_lengths_eq hchain
        _ = mapWork.length := by simpa using hmapLen
    rw [List.length_zipWith, hfeatureLen]
    simpa [hwork]
  simpa [localWork] using theorem41_runtimeReduction_closed hb hchain hlen

/-- Current-form arithmetic corollaries of Theorem 4.1. Besides the paper-facing runtime bound,
we also retain the stronger uniform-payload and closed-form arithmetic estimates derived above. -/
theorem theorem41_current
    {b : Nat} {x rs : Program} {fs gs : List Program}
    {featureWork mapWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hfeatureLen : fs.length = featureWork.length)
    (hmapLen : gs.length = mapWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      branchSearchTimeBound fs gs (List.zipWith (· + ·) featureWork mapWork) =
        (branchSearchTimeExplicitTerms fs gs
          (List.zipWith (· + ·) featureWork mapWork)).sum ∧
      (branchSearchTimeExplicitTerms fs gs
          (List.zipWith (· + ·) featureWork mapWork)).sum ≤
        (uniformBranchSearchTimeTerms (autoencoderPayloadBound b)
          (List.zipWith (· + ·) featureWork mapWork)).sum ∧
      branchSearchTimeBound fs gs (List.zipWith (· + ·) featureWork mapWork) ≤
        ((List.zipWith (· + ·) featureWork mapWork).sum +
            (List.zipWith (· + ·) featureWork mapWork).length) *
          2 ^ ((autoencoderPayloadBound b + 1) *
            (List.zipWith (· + ·) featureWork mapWork).length) := by
  obtain ⟨node, hnode, hdesc, hruns, hexact, huniform⟩ :=
    theorem41_runtimeReduction_explicit_split hb hchain hfeatureLen hmapLen
  obtain ⟨_, _, _, _, hclosed⟩ :=
    theorem41_runtimeReduction_closed_split hb hchain hfeatureLen hmapLen
  exact ⟨node, hnode, hdesc, hruns, hexact, huniform, hclosed⟩

/-- Paper-form Theorem 4.1 for the Section 3.5 incremental `b`-compression scheme. ALICE finds
the branch carrying the features `f₁, ..., fₛ` and description `D_s = ⟨s, r_s, f_s, ..., f_1⟩`, and
the total search time is bounded by the paper-style weighted sum with cumulative exponent
`∑_{k≤i} (l(f_k) + l(f_k') + autoencoderPaperOverhead b)`, i.e. by
`∑ (t_i + t_i' + 1) 2^{∑_{k≤i}(l(f_k) + l(f_k')) + O(i)}`. -/
theorem theorem41
    {b : Nat} {x rs : Program} {fs gs : List Program}
    {featureWork mapWork : List Nat}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hfeatureLen : fs.length = featureWork.length)
    (hmapLen : gs.length = mapWork.length) :
    ∃ node, IsAliceBranch x node ∧ node.features = fs ∧
      node.description = schemeDescription rs fs ∧
      runs schemeDescriptionInterpreter node.description x ∧
      branchSearchTimeBound fs gs (List.zipWith (· + ·) featureWork mapWork) ≤
        (branchSearchTimePaperExplicitTerms b fs gs
          (List.zipWith (· + ·) featureWork mapWork)).sum := by
  let localWork := List.zipWith (· + ·) featureWork mapWork
  have hlen : fs.length = localWork.length := by
    have hwork : featureWork.length = mapWork.length := by
      calc
        featureWork.length = fs.length := by simpa using hfeatureLen.symm
        _ = gs.length := incrementalBCompressionScheme_lengths_eq hchain
        _ = mapWork.length := by simpa using hmapLen
    rw [List.length_zipWith, hfeatureLen]
    have hle : featureWork.length ≤ mapWork.length := by
      omega
    exact (Nat.min_eq_left hle).symm
  obtain ⟨node, hnode, hfeatures, hdesc, hruns⟩ := theorem41_semantic hchain
  have hbound :
      branchSearchTimeBound fs gs localWork ≤ branchSearchTimePaperBound b fs gs localWork := by
    exact branchSearchTimeBound_le_paper
      (incrementalBCompressionScheme_stepExponent_paperBound hb hchain) hlen
  refine ⟨node, hnode, hfeatures, hdesc, hruns, ?_⟩
  simpa [localWork] using
    (le_trans hbound (le_of_eq (branchSearchTimePaperBound_eq_sum_explicitTerms b fs gs localWork)))

end

end Compression

end IcTheory
