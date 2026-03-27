import IcTheory.Compression.Section4
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace IcTheory

namespace Compression

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

end

end Compression

end IcTheory
