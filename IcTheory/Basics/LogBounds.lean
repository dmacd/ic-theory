import IcTheory.Basics.BitString
import Mathlib.Data.Nat.Log

namespace IcTheory

/-- The logarithmic penalty we use for "up to logarithmic overhead" statements. -/
def logPenalty (n : Nat) : Nat := Nat.log2 (n + 1)

/-- `LogLe a b n` means `a` is bounded by `b` up to a linear function of `logPenalty n`. -/
def LogLe (a b n : Nat) : Prop :=
  ∃ c d : Nat, a ≤ b + c * logPenalty n + d

/-- Symmetric logarithmic slack. -/
def LogEq (a b n : Nat) : Prop :=
  LogLe a b n ∧ LogLe b a n

@[simp] theorem logPenalty_zero : logPenalty 0 = 0 := by
  rw [logPenalty, Nat.log2_def]
  decide

theorem logPenalty_pos (n : Nat) : 0 ≤ logPenalty n := by
  exact Nat.zero_le _

theorem logLe_of_le {a b n : Nat} (h : a ≤ b) : LogLe a b n := by
  refine ⟨0, 0, ?_⟩
  simpa [LogLe, logPenalty] using h

theorem logLe_refl (a n : Nat) : LogLe a a n :=
  logLe_of_le (a := a) (b := a) (n := n) le_rfl

theorem logEq_refl (a n : Nat) : LogEq a a n := by
  exact ⟨logLe_refl a n, logLe_refl a n⟩

theorem logLe_trans {a b c n : Nat} (hab : LogLe a b n) (hbc : LogLe b c n) : LogLe a c n := by
  rcases hab with ⟨c₁, d₁, h₁⟩
  rcases hbc with ⟨c₂, d₂, h₂⟩
  have hsum : a ≤ c + c₂ * logPenalty n + d₂ + (c₁ * logPenalty n + d₁) := by
    omega
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  calc
    a ≤ c + c₂ * logPenalty n + d₂ + (c₁ * logPenalty n + d₁) := hsum
    _ = c + (c₁ + c₂) * logPenalty n + (d₁ + d₂) := by
      rw [Nat.add_mul]
      omega

theorem LogEq.symm {a b n : Nat} (h : LogEq a b n) : LogEq b a n :=
  ⟨h.2, h.1⟩

theorem LogEq.trans {a b c n : Nat} (hab : LogEq a b n) (hbc : LogEq b c n) : LogEq a c n := by
  exact ⟨logLe_trans hab.1 hbc.1, logLe_trans hbc.2 hab.2⟩

theorem blen_ofNat_le_logPenalty_succ (n : Nat) :
    BitString.blen (BitString.ofNat n) ≤ logPenalty n + 1 := by
  rw [BitString.blen_ofNat_eq_size, logPenalty]
  calc
    Nat.size n ≤ Nat.log2 n + 1 := by
      rw [Nat.log2_eq_log_two]
      exact Nat.size_le.2 (Nat.lt_pow_succ_log_self Nat.one_lt_two n)
    _ ≤ Nat.log2 (n + 1) + 1 := by
      exact Nat.add_le_add_right (by
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
        exact Nat.log_mono_right (Nat.le_add_right n 1)) 1

end IcTheory
