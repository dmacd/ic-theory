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

theorem logPenalty_mono {m n : Nat} (h : m ≤ n) : logPenalty m ≤ logPenalty n := by
  unfold logPenalty
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right (Nat.succ_le_succ h)

theorem logPenalty_le_self (n : Nat) : logPenalty n ≤ n := by
  unfold logPenalty
  exact Nat.le_of_lt_succ (by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.succ_ne_zero n) (show n + 1 < 2 ^ (n + 1) from Nat.lt_two_pow_self))

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

theorem logLe_add {a b c d n : Nat}
    (hab : LogLe a b n)
    (hcd : LogLe c d n) :
    LogLe (a + c) (b + d) n := by
  rcases hab with ⟨c₁, d₁, h₁⟩
  rcases hcd with ⟨c₂, d₂, h₂⟩
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  calc
    a + c ≤ (b + c₁ * logPenalty n + d₁) + (d + c₂ * logPenalty n + d₂) := by
      exact Nat.add_le_add h₁ h₂
    _ = b + d + (c₁ + c₂) * logPenalty n + (d₁ + d₂) := by
      rw [Nat.add_mul]
      omega

theorem LogEq.symm {a b n : Nat} (h : LogEq a b n) : LogEq b a n :=
  ⟨h.2, h.1⟩

theorem LogEq.trans {a b c n : Nat} (hab : LogEq a b n) (hbc : LogEq b c n) : LogEq a c n := by
  exact ⟨logLe_trans hab.1 hbc.1, logLe_trans hbc.2 hab.2⟩

theorem logLe_of_scale_le {a b m n : Nat} (hab : LogLe a b m) (hmn : m ≤ n) : LogLe a b n := by
  rcases hab with ⟨c, d, h⟩
  have hlog : c * logPenalty m ≤ c * logPenalty n :=
    Nat.mul_le_mul_left c (logPenalty_mono hmn)
  refine ⟨c, d, ?_⟩
  omega

theorem logEq_of_scale_le {a b m n : Nat} (hab : LogEq a b m) (hmn : m ≤ n) : LogEq a b n := by
  exact ⟨logLe_of_scale_le hab.1 hmn, logLe_of_scale_le hab.2 hmn⟩

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

theorem logPenalty_four_mul_add_three (n : Nat) :
    logPenalty (4 * n + 3) = logPenalty n + 2 := by
  unfold logPenalty
  rw [show 4 * n + 3 + 1 = (n + 1) * 2 * 2 by omega]
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have h1 : Nat.log 2 ((n + 1) * 2 * 2) = Nat.log 2 ((n + 1) * 2) + 1 := by
    rw [Nat.log_mul_base Nat.one_lt_two (Nat.mul_ne_zero (Nat.succ_ne_zero _) (by decide))]
  have h2 : Nat.log 2 ((n + 1) * 2) = Nat.log 2 (n + 1) + 1 := by
    rw [Nat.log_mul_base Nat.one_lt_two (Nat.succ_ne_zero _)]
  rw [h1, h2]

theorem logPenalty_twoPow_mul_succ_sub_one (n k : Nat) :
    logPenalty ((n + 1) * 2 ^ k - 1) = logPenalty n + k := by
  induction k with
  | zero =>
      simp [logPenalty]
  | succ k ih =>
      have hne : (n + 1) * 2 ^ k ≠ 0 := by
        exact Nat.mul_ne_zero (Nat.succ_ne_zero _) (pow_ne_zero _ (by decide))
      have hpos' : 0 < (n + 1) * 2 ^ k := by
        exact Nat.mul_pos (Nat.succ_pos _) (pow_pos (by decide) _)
      have hpos : 0 < ((n + 1) * 2 ^ k) * 2 := by
        exact Nat.mul_pos hpos' (by decide)
      unfold logPenalty
      rw [Nat.log2_eq_log_two]
      rw [show ((n + 1) * 2 ^ (k + 1) - 1) + 1 = ((n + 1) * 2 ^ k) * 2 by
        rw [pow_succ]
        rw [Nat.mul_assoc]
        simpa [Nat.mul_assoc] using Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
      rw [Nat.log_mul_base Nat.one_lt_two hne]
      have hadd : ((n + 1) * 2 ^ k - 1) + 1 = (n + 1) * 2 ^ k := by
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos')
      have hlogk : Nat.log 2 ((n + 1) * 2 ^ k) = logPenalty ((n + 1) * 2 ^ k - 1) := by
        rw [logPenalty, Nat.log2_eq_log_two, hadd]
      rw [hlogk]
      simpa [Nat.add_assoc] using congrArg Nat.succ ih

theorem logPenalty_le_of_le_twoPow_mul_succ_sub_one {m n k : Nat}
    (h : m ≤ (n + 1) * 2 ^ k - 1) :
    logPenalty m ≤ logPenalty n + k := by
  have hmono : logPenalty m ≤ logPenalty ((n + 1) * 2 ^ k - 1) := logPenalty_mono h
  rw [logPenalty_twoPow_mul_succ_sub_one] at hmono
  exact hmono

theorem logPenalty_add_le (m n : Nat) :
    logPenalty (m + n) ≤ logPenalty m + logPenalty n + 1 := by
  let a : Nat := 2 ^ (logPenalty n + 1)
  have ha : n + 1 ≤ a := by
    dsimp [a]
    unfold logPenalty
    rw [Nat.log2_eq_log_two]
    exact Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two (n + 1))
  have ha1 : 1 ≤ a := by
    exact le_trans (Nat.succ_le_succ (Nat.zero_le n)) ha
  have hsum : m + n ≤ (m + 1) * a - 1 := by
    have hn : n ≤ a - 1 := by
      omega
    calc
      m + n ≤ m + (a - 1) := by omega
      _ ≤ m * a + (a - 1) := by
        exact Nat.add_le_add_right (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left m ha1) _
      _ = (m + 1) * a - 1 := by
        rw [Nat.add_mul, one_mul, Nat.add_sub_assoc ha1]
  have hlog :=
    logPenalty_le_of_le_twoPow_mul_succ_sub_one
      (m := m + n) (n := m) (k := logPenalty n + 1) (by simpa [a] using hsum)
  omega

theorem logPenalty_le_of_le_log_scale {m n c d : Nat}
    (h : m ≤ n + c * logPenalty n + d) :
    logPenalty m ≤ logPenalty n + (c + d + 2) := by
  let a : Nat := 2 ^ (c + d + 2)
  have habig : c + d + 2 ≤ a := by
    dsimp [a]
    exact Nat.le_of_lt (show c + d + 2 < 2 ^ (c + d + 2) from Nat.lt_two_pow_self)
  have ha1 : 1 ≤ a := by
    exact le_trans (by omega) habig
  have hac : c + 1 ≤ a := by
    exact le_trans (by omega) habig
  have had : d + 1 ≤ a := by
    exact le_trans (by omega) habig
  have hconst : d ≤ a - 1 := by
    exact Nat.le_sub_one_of_lt (lt_of_lt_of_le (Nat.lt_succ_self d) had)
  have hm : m ≤ (n + 1) * a - 1 := by
    have hlog := logPenalty_le_self n
    calc
      m ≤ n + c * logPenalty n + d := h
      _ ≤ n + c * n + d := by
        have hc : c * logPenalty n ≤ c * n := Nat.mul_le_mul_left c hlog
        omega
      _ = (c + 1) * n + d := by
        calc
          n + c * n + d = c * n + n + d := by ac_rfl
          _ = (c + 1) * n + d := by rw [Nat.add_mul, one_mul]
      _ ≤ a * n + (a - 1) := by
        have hmul : (c + 1) * n ≤ a * n := Nat.mul_le_mul_right n hac
        exact Nat.add_le_add hmul hconst
      _ = (n + 1) * a - 1 := by
        calc
          a * n + (a - 1) = a * n + a - 1 := by rw [Nat.add_sub_assoc ha1]
          _ = n * a + a - 1 := by rw [Nat.mul_comm]
          _ = (n + 1) * a - 1 := by rw [Nat.add_mul, one_mul]
  have hmono : logPenalty m ≤ logPenalty ((n + 1) * a - 1) := logPenalty_mono hm
  dsimp [a] at hmono ⊢
  rw [logPenalty_twoPow_mul_succ_sub_one] at hmono
  exact hmono

theorem logLe_of_scale_logLe {a b m n : Nat}
    (hab : LogLe a b m)
    (hmn : LogLe m n n) :
    LogLe a b n := by
  rcases hab with ⟨c₁, d₁, h₁⟩
  rcases hmn with ⟨c₂, d₂, h₂⟩
  have hlog :
      logPenalty m ≤ logPenalty n + (c₂ + d₂ + 2) :=
    logPenalty_le_of_le_log_scale h₂
  have hmul : c₁ * logPenalty m ≤ c₁ * (logPenalty n + (c₂ + d₂ + 2)) := by
    exact Nat.mul_le_mul_left c₁ hlog
  refine ⟨c₁, c₁ * (c₂ + d₂ + 2) + d₁, ?_⟩
  calc
    a ≤ b + c₁ * logPenalty m + d₁ := h₁
    _ ≤ b + c₁ * (logPenalty n + (c₂ + d₂ + 2)) + d₁ := by
      omega
    _ = b + c₁ * logPenalty n + (c₁ * (c₂ + d₂ + 2) + d₁) := by
      rw [Nat.mul_add]
      omega

theorem logEq_of_scale_logLe {a b m n : Nat}
    (hab : LogEq a b m)
    (hmn : LogLe m n n) :
    LogEq a b n := by
  exact ⟨logLe_of_scale_logLe hab.1 hmn, logLe_of_scale_logLe hab.2 hmn⟩

theorem blen_ofNat_le_logPenalty_add_three_of_le_four_mul_add_three {m n : Nat}
    (h : m ≤ 4 * n + 3) :
    BitString.blen (BitString.ofNat m) ≤ logPenalty n + 3 := by
  have hlog : logPenalty m ≤ logPenalty (4 * n + 3) := logPenalty_mono h
  have hsize := blen_ofNat_le_logPenalty_succ m
  rw [logPenalty_four_mul_add_three] at hlog
  omega

theorem blen_ofNat_le_logPenalty_add_of_le_twoPow_mul_succ_sub_one {m n k : Nat}
    (h : m ≤ (n + 1) * 2 ^ k - 1) :
    BitString.blen (BitString.ofNat m) ≤ logPenalty n + k + 1 := by
  have hlog : logPenalty m ≤ logPenalty ((n + 1) * 2 ^ k - 1) := logPenalty_mono h
  have hsize := blen_ofNat_le_logPenalty_succ m
  rw [logPenalty_twoPow_mul_succ_sub_one] at hlog
  omega

end IcTheory
