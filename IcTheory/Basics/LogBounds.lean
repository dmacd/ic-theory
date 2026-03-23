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

theorem LogEq.symm {a b n : Nat} (h : LogEq a b n) : LogEq b a n :=
  ⟨h.2, h.1⟩

end IcTheory
