import IcTheory.Compression.Theorem34

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- `StepLogLe a b s n` means that `a` is bounded by `b` up to `s` many logarithmic-overhead
steps at ambient scale `n`. This is the bookkeeping relation needed for iterating single-step
compression bounds in Theorem 3.6. -/
def StepLogLe (a b s n : Nat) : Prop :=
  ∃ c d : Nat, a ≤ b + s * (c * logPenalty n + d)

/-- Symmetric `s`-step logarithmic slack. -/
def StepLogEq (a b s n : Nat) : Prop :=
  StepLogLe a b s n ∧ StepLogLe b a s n

theorem stepLogLe_of_logLe {a b n : Nat} (h : LogLe a b n) :
    StepLogLe a b 1 n := by
  rcases h with ⟨c, d, hcd⟩
  refine ⟨c, d, ?_⟩
  omega

theorem stepLogEq_of_logEq {a b n : Nat} (h : LogEq a b n) :
    StepLogEq a b 1 n := by
  exact ⟨stepLogLe_of_logLe h.1, stepLogLe_of_logLe h.2⟩

theorem stepLogLe_refl (a n : Nat) : StepLogLe a a 0 n := by
  refine ⟨0, 0, ?_⟩
  simp

theorem stepLogEq_refl (a n : Nat) : StepLogEq a a 0 n := by
  exact ⟨stepLogLe_refl a n, stepLogLe_refl a n⟩

theorem stepLogLe_of_scale_le {a b s m n : Nat}
    (hab : StepLogLe a b s m) (hmn : m ≤ n) :
    StepLogLe a b s n := by
  rcases hab with ⟨c, d, hcd⟩
  refine ⟨c, d, ?_⟩
  have hlog : c * logPenalty m ≤ c * logPenalty n := by
    exact Nat.mul_le_mul_left c (logPenalty_mono hmn)
  have hstep :
      s * (c * logPenalty m + d) ≤ s * (c * logPenalty n + d) := by
    exact Nat.mul_le_mul_left s (Nat.add_le_add_right hlog d)
  exact le_trans hcd (by omega)

theorem stepLogEq_of_scale_le {a b s m n : Nat}
    (hab : StepLogEq a b s m) (hmn : m ≤ n) :
    StepLogEq a b s n := by
  exact ⟨stepLogLe_of_scale_le hab.1 hmn, stepLogLe_of_scale_le hab.2 hmn⟩

theorem stepLogLe_trans {a b c s t n : Nat}
    (hab : StepLogLe a b s n) (hbc : StepLogLe b c t n) :
    StepLogLe a c (s + t) n := by
  rcases hab with ⟨c₁, d₁, h₁⟩
  rcases hbc with ⟨c₂, d₂, h₂⟩
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  have hsum :
      a ≤ c + s * (c₁ * logPenalty n + d₁) + t * (c₂ * logPenalty n + d₂) := by
    omega
  have hbound :
      s * (c₁ * logPenalty n + d₁) + t * (c₂ * logPenalty n + d₂) ≤
        (s + t) * ((c₁ + c₂) * logPenalty n + (d₁ + d₂)) := by
    let q := (c₁ + c₂) * logPenalty n + (d₁ + d₂)
    have hs :
        s * (c₁ * logPenalty n + d₁) ≤ s * q := by
      have hq₁ : c₁ * logPenalty n + d₁ ≤ q := by
        dsimp [q]
        have hc :
            c₁ * logPenalty n ≤ (c₁ + c₂) * logPenalty n := by
          exact Nat.mul_le_mul_right _ (Nat.le_add_right c₁ c₂)
        exact Nat.add_le_add hc (Nat.le_add_right d₁ d₂)
      exact Nat.mul_le_mul_left s hq₁
    have ht :
        t * (c₂ * logPenalty n + d₂) ≤ t * q := by
      have hq₂ : c₂ * logPenalty n + d₂ ≤ q := by
        dsimp [q]
        have hc :
            c₂ * logPenalty n ≤ (c₁ + c₂) * logPenalty n := by
          exact Nat.mul_le_mul_right _ (Nat.le_add_left c₂ c₁)
        exact Nat.add_le_add hc (Nat.le_add_left d₂ d₁)
      exact Nat.mul_le_mul_left t hq₂
    calc
      s * (c₁ * logPenalty n + d₁) + t * (c₂ * logPenalty n + d₂) ≤ s * q + t * q := by
        exact Nat.add_le_add hs ht
      _ = (s + t) * q := by
        rw [Nat.add_mul]
      _ = (s + t) * ((c₁ + c₂) * logPenalty n + (d₁ + d₂)) := by
        rfl
  exact le_trans hsum (by omega)

theorem stepLogEq_trans {a b c s t n : Nat}
    (hab : StepLogEq a b s n) (hbc : StepLogEq b c t n) :
    StepLogEq a c (s + t) n := by
  refine ⟨stepLogLe_trans hab.1 hbc.1, ?_⟩
  simpa [Nat.add_comm] using stepLogLe_trans hbc.2 hab.2

theorem stepLogLe_add_left {a b k s n : Nat}
    (hab : StepLogLe a b s n) :
    StepLogLe (k + a) (k + b) s n := by
  rcases hab with ⟨c, d, hcd⟩
  refine ⟨c, d, ?_⟩
  omega

theorem stepLogLe_of_stepCount_le {a b s t n : Nat}
    (hab : StepLogLe a b s n)
    (hst : s ≤ t) :
    StepLogLe a b t n := by
  rcases hab with ⟨c, d, hcd⟩
  refine ⟨c, d, ?_⟩
  have hmul :
      s * (c * logPenalty n + d) ≤
        t * (c * logPenalty n + d) := by
    exact Nat.mul_le_mul_right _ hst
  exact le_trans hcd (by omega)

theorem stepLogLe_add {a b s t n : Nat}
    (ha : StepLogLe a 0 s n)
    (hb : StepLogLe b 0 t n) :
    StepLogLe (a + b) 0 (s + t) n := by
  rcases ha with ⟨c₁, d₁, h₁⟩
  rcases hb with ⟨c₂, d₂, h₂⟩
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  have hsum :
      a + b ≤
        s * (c₁ * logPenalty n + d₁) +
          t * (c₂ * logPenalty n + d₂) := by
    omega
  have hbound :
      s * (c₁ * logPenalty n + d₁) + t * (c₂ * logPenalty n + d₂) ≤
        (s + t) * ((c₁ + c₂) * logPenalty n + (d₁ + d₂)) := by
    let q := (c₁ + c₂) * logPenalty n + (d₁ + d₂)
    have hs :
        s * (c₁ * logPenalty n + d₁) ≤ s * q := by
      have hq₁ : c₁ * logPenalty n + d₁ ≤ q := by
        dsimp [q]
        have hc :
            c₁ * logPenalty n ≤ (c₁ + c₂) * logPenalty n := by
          exact Nat.mul_le_mul_right _ (Nat.le_add_right c₁ c₂)
        exact Nat.add_le_add hc (Nat.le_add_right d₁ d₂)
      exact Nat.mul_le_mul_left s hq₁
    have ht :
        t * (c₂ * logPenalty n + d₂) ≤ t * q := by
      have hq₂ : c₂ * logPenalty n + d₂ ≤ q := by
        dsimp [q]
        have hc :
            c₂ * logPenalty n ≤ (c₁ + c₂) * logPenalty n := by
          exact Nat.mul_le_mul_right _ (Nat.le_add_left c₂ c₁)
        exact Nat.add_le_add hc (Nat.le_add_left d₂ d₁)
      exact Nat.mul_le_mul_left t hq₂
    calc
      s * (c₁ * logPenalty n + d₁) + t * (c₂ * logPenalty n + d₂) ≤ s * q + t * q := by
        exact Nat.add_le_add hs ht
      _ = (s + t) * q := by
        rw [Nat.add_mul]
      _ = (s + t) * ((c₁ + c₂) * logPenalty n + (d₁ + d₂)) := by
        rfl
  simpa using le_trans hsum hbound

theorem logLe_of_stepLogLe {a b s n : Nat}
    (hab : StepLogLe a b s n) :
    LogLe a b n := by
  rcases hab with ⟨c, d, hcd⟩
  refine ⟨s * c, s * d, ?_⟩
  have hscale :
      s * (c * logPenalty n + d) ≤
        (s * c) * logPenalty n + s * d := by
    rw [Nat.mul_add, Nat.mul_assoc]
  calc
    a ≤ b + s * (c * logPenalty n + d) := hcd
    _ ≤ b + ((s * c) * logPenalty n + s * d) := by
      exact Nat.add_le_add_left hscale b
    _ = b + (s * c) * logPenalty n + s * d := by
      omega

theorem stepLogEq_add_left {a b k s n : Nat}
    (hab : StepLogEq a b s n) :
    StepLogEq (k + a) (k + b) s n := by
  exact ⟨stepLogLe_add_left hab.1, stepLogLe_add_left hab.2⟩

theorem StepLogEq.symm {a b s n : Nat}
    (hab : StepLogEq a b s n) :
    StepLogEq b a s n := by
  exact ⟨hab.2, hab.1⟩

theorem stepLogEq_of_stepCount_le {a b s t n : Nat}
    (hab : StepLogEq a b s n)
    (hst : s ≤ t) :
    StepLogEq a b t n := by
  exact ⟨stepLogLe_of_stepCount_le hab.1 hst,
    stepLogLe_of_stepCount_le hab.2 hst⟩

/-- Prefix-complexity content of a feature list. This is the current formalization-level replacement
for the paper's eventual `∑ l(fᵢ*)`, which will follow once the incompressibility bridge for
shortest features is fully packaged. -/
def featurePrefixComplexitySum (fs : List Program) : Nat :=
  (fs.map PrefixComplexity).sum

@[simp] theorem featurePrefixComplexitySum_nil :
    featurePrefixComplexitySum [] = 0 := by
  rfl

@[simp] theorem featurePrefixComplexitySum_cons (f : Program) (fs : List Program) :
    featurePrefixComplexitySum (f :: fs) =
      PrefixComplexity f + featurePrefixComplexitySum fs := by
  simp [featurePrefixComplexitySum]

/-- One compression step in the current prefix-facing theory: `f` is a shortest feature of `x`
with residual `r`, and the two extra hypotheses are exactly the bridges already isolated in the
Section 3 development. -/
def IsPrefixCompressionStep (x f r : Program) : Prop :=
  IsShortestFeature runs f x ∧
    runs f r x ∧
    CompressionCondition f r x ∧
    BitString.blen f ≤ PrefixConditionalComplexity x r ∧
    NoSuperfluousPair r f x

private theorem residual_length_lt_of_prefixCompressionStep {x f r : Program}
    (hstep : IsPrefixCompressionStep x f r) :
    BitString.blen r < BitString.blen x := by
  rcases hstep with ⟨_, _, hcomp, _, _⟩
  unfold CompressionCondition at hcomp
  omega

/-- Paper-facing inductive model of incremental compression, stopping with the final residual
`rs`. The feature list is ordered as `f₁, ..., fₛ`. -/
inductive IsIncrementalPrefixCompression : Program → List Program → Program → Prop
  | nil (x : Program) :
      IsIncrementalPrefixCompression x [] x
  | cons {x f r rs : Program} {fs : List Program}
      (hstep : IsPrefixCompressionStep x f r)
      (hrest : IsIncrementalPrefixCompression r fs rs) :
      IsIncrementalPrefixCompression x (f :: fs) rs

/-- A single prefix compression step already gives the one-step form of the Theorem 3.6
decomposition. -/
theorem stepLogEq_of_prefixCompressionStep {x f r : Program}
    (hstep : IsPrefixCompressionStep x f r) :
    StepLogEq (PrefixComplexity x)
      (PrefixComplexity f + PrefixComplexity r)
      1
      (BitString.blen x) := by
  rcases hstep with ⟨_hshort, hf, hcomp, hshortPrefix, hpair⟩
  exact stepLogEq_of_logEq <|
    theorem34_eq28_of_prefixShortestBridge_and_noSuperfluousPair hshortPrefix hf hcomp hpair

/-- Prefix-form Theorem 3.6: iterating the current single-step decomposition yields a total
description length equal to the sum of feature prefix complexities plus the last residual
complexity, up to `s` logarithmic overhead terms at the original ambient scale `l(x)`. -/
theorem theorem36_prefix {x rs : Program} {fs : List Program}
    (hchain : IsIncrementalPrefixCompression x fs rs) :
    StepLogEq (PrefixComplexity x)
      (featurePrefixComplexitySum fs + PrefixComplexity rs)
      fs.length
      (BitString.blen x) := by
  induction hchain with
  | nil x =>
      simpa using stepLogEq_refl (PrefixComplexity x) (BitString.blen x)
  | @cons x f r rs fs hstep hrest ih =>
      have hstepEq :
          StepLogEq (PrefixComplexity x)
            (PrefixComplexity f + PrefixComplexity r)
            1
            (BitString.blen x) :=
        stepLogEq_of_prefixCompressionStep hstep
      have hrestEq :
          StepLogEq (PrefixComplexity r)
            (featurePrefixComplexitySum fs + PrefixComplexity rs)
            fs.length
            (BitString.blen x) := by
        exact stepLogEq_of_scale_le ih (residual_length_lt_of_prefixCompressionStep hstep).le
      have hrestAdd :
          StepLogEq (PrefixComplexity f + PrefixComplexity r)
            (PrefixComplexity f + (featurePrefixComplexitySum fs + PrefixComplexity rs))
            fs.length
            (BitString.blen x) := by
        exact stepLogEq_add_left hrestEq
      have htotal :
          StepLogEq (PrefixComplexity x)
            (PrefixComplexity f + (featurePrefixComplexitySum fs + PrefixComplexity rs))
            (1 + fs.length)
            (BitString.blen x) := by
        exact stepLogEq_trans hstepEq hrestAdd
      simpa [featurePrefixComplexitySum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        htotal

end

end Compression

end IcTheory
