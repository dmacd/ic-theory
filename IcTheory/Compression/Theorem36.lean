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

/-- Exact feature-length content of a feature list. This is the paper-facing quantity
`∑ l(fᵢ*)` from Theorem 3.6. -/
def featureLengthSum (fs : List Program) : Nat :=
  (fs.map BitString.blen).sum

@[simp] theorem featureLengthSum_nil :
    featureLengthSum [] = 0 := by
  rfl

@[simp] theorem featureLengthSum_cons (f : Program) (fs : List Program) :
    featureLengthSum (f :: fs) =
      BitString.blen f + featureLengthSum fs := by
  simp [featureLengthSum]

/-- One compression step in the current prefix-facing theory: `f` is a shortest feature of `x`
with residual `r`, and the two extra hypotheses are exactly the bridges already isolated in the
Section 3 development. -/
def IsPrefixCompressionStep (x f r : Program) : Prop :=
  IsShortestFeature runs f x ∧
    runs f r x ∧
    CompressionCondition f r x ∧
    BitString.blen f ≤ PrefixConditionalComplexity x r ∧
    NoSuperfluousPair r f x

/-- One exact-length compression step in the paper-facing theory: `f` is a shortest feature of
`x`, `r` is a residual with no superfluous overlap with `f`, and the compression condition holds. -/
def IsCompressionStep (x f r : Program) : Prop :=
  IsShortestFeature runs f x ∧
    runs f r x ∧
    CompressionCondition f r x ∧
    NoSuperfluousPair r f x

/-- One compression step in the paper-form Theorem 3.6 packaging:
`f*` is a shortest feature of `x`, `f'^*` is a shortest corresponding descriptive map, and
`r = f'^*(x)` is the residual description used in the paper statement. -/
def IsPaperCompressionStep (x f r : Program) : Prop :=
  ∃ g : Program,
    IsShortestFeature runs f x ∧
      IsShortestDescriptiveMap runs f g x ∧
      runs g x r ∧
      runs f r x ∧
      CompressionCondition f r x

private theorem residual_length_lt_of_compressionStep {x f r : Program}
    (hstep : IsCompressionStep x f r) :
    BitString.blen r < BitString.blen x := by
  rcases hstep with ⟨_, _, hcomp, _⟩
  unfold CompressionCondition at hcomp
  omega

private theorem residual_length_lt_of_prefixCompressionStep {x f r : Program}
    (hstep : IsPrefixCompressionStep x f r) :
    BitString.blen r < BitString.blen x := by
  rcases hstep with ⟨_, _, hcomp, _, _⟩
  unfold CompressionCondition at hcomp
  omega

private theorem residual_length_lt_of_paperCompressionStep {x f r : Program}
    (hstep : IsPaperCompressionStep x f r) :
    BitString.blen r < BitString.blen x := by
  rcases hstep with ⟨_, _, _, _, _, hcomp⟩
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

private theorem logEq_add_left {a b k n : Nat}
    (hab : LogEq a b n) :
    LogEq (k + a) (k + b) n := by
  exact ⟨logLe_add (logLe_refl k n) hab.1, logLe_add (logLe_refl k n) hab.2⟩

/-- A single exact-length compression step already gives the one-step form of the paper's
Theorem 3.6 decomposition. -/
theorem stepLogEq_of_compressionStep {x f r : Program}
    (hstep : IsCompressionStep x f r) :
    StepLogEq (PrefixComplexity x)
      (BitString.blen f + PrefixComplexity r)
      1
      (BitString.blen x) := by
  rcases hstep with ⟨hshort, hf, hcomp, hpair⟩
  have hstepEq :
      LogEq (PrefixComplexity x)
        (PrefixComplexity f + PrefixComplexity r)
        (BitString.blen x) :=
    theorem34_eq28_of_shortestFeature_and_noSuperfluousPair hshort hf hcomp hpair
  have hfeatureEq :
      LogEq (PrefixComplexity f + PrefixComplexity r)
        (BitString.blen f + PrefixComplexity r)
        (BitString.blen x) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (logEq_add_left (k := PrefixComplexity r) (theorem31 hshort))
  exact stepLogEq_of_logEq (hstepEq.trans hfeatureEq)

/-- A single paper-facing compression step already gives the one-step form of Theorem 3.6. -/
theorem stepLogEq_of_paperCompressionStep {x f r : Program}
    (hstep : IsPaperCompressionStep x f r) :
    StepLogEq (PrefixComplexity x)
      (BitString.blen f + PrefixComplexity r)
      1
      (BitString.blen x) := by
  rcases hstep with ⟨g, hshortF, hshortG, hr, hf, hcomp⟩
  have hstepEq :
      LogEq (PrefixComplexity x)
        (PrefixComplexity f + PrefixComplexity r)
        (BitString.blen x) :=
    theorem34_eq28 hshortF hshortG hr hf hcomp
  have hfeatureEq :
      LogEq (PrefixComplexity f + PrefixComplexity r)
        (BitString.blen f + PrefixComplexity r)
        (BitString.blen x) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (logEq_add_left (k := PrefixComplexity r) (theorem31 hshortF))
  exact stepLogEq_of_logEq (hstepEq.trans hfeatureEq)

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

/-- Paper-facing inductive model of incremental compression. The feature list is ordered as
`f₁, ..., fₛ`, and each residual witness is chosen so that the corresponding feature/residual pair
already satisfies the no-superfluous-information conclusion from Theorem 3.4. -/
inductive IsIncrementalCompression : Program → List Program → Program → Prop
  | nil (x : Program) :
      IsIncrementalCompression x [] x
  | cons {x f r rs : Program} {fs : List Program}
      (hstep : IsCompressionStep x f r)
      (hrest : IsIncrementalCompression r fs rs) :
      IsIncrementalCompression x (f :: fs) rs

/-- Paper-form inductive model of incremental compression from Theorem 3.6:
`r₀ ≡ x`, each `fᵢ*` is a shortest feature of `rᵢ₋₁`, and `rᵢ` is a corresponding residual
description produced by the corresponding shortest descriptive map `fᵢ'^*`. -/
inductive IsIncrementalPaperCompression : Program → List Program → Program → Prop
  | nil (x : Program) :
      IsIncrementalPaperCompression x [] x
  | cons {x f r rs : Program} {fs : List Program}
      (hstep : IsPaperCompressionStep x f r)
      (hrest : IsIncrementalPaperCompression r fs rs) :
      IsIncrementalPaperCompression x (f :: fs) rs

/-- Exact-length Theorem 3.6:
iterating shortest-feature compression with no-superfluous residual witnesses yields a total
description length equal to `∑ l(fᵢ*) + K(rₛ)` up to `s` logarithmic overhead terms. -/
theorem theorem36 {x rs : Program} {fs : List Program}
    (hchain : IsIncrementalCompression x fs rs) :
    StepLogEq (PrefixComplexity x)
      (featureLengthSum fs + PrefixComplexity rs)
      fs.length
      (BitString.blen x) := by
  induction hchain with
  | nil x =>
      simpa using stepLogEq_refl (PrefixComplexity x) (BitString.blen x)
  | @cons x f r rs fs hstep hrest ih =>
      have hstepEq :
          StepLogEq (PrefixComplexity x)
            (BitString.blen f + PrefixComplexity r)
            1
            (BitString.blen x) :=
        stepLogEq_of_compressionStep hstep
      have hrestEq :
          StepLogEq (PrefixComplexity r)
            (featureLengthSum fs + PrefixComplexity rs)
            fs.length
            (BitString.blen x) := by
        exact stepLogEq_of_scale_le ih (residual_length_lt_of_compressionStep hstep).le
      have hrestAdd :
          StepLogEq (BitString.blen f + PrefixComplexity r)
            (BitString.blen f + (featureLengthSum fs + PrefixComplexity rs))
            fs.length
            (BitString.blen x) := by
        exact stepLogEq_add_left hrestEq
      have htotal :
          StepLogEq (PrefixComplexity x)
            (BitString.blen f + (featureLengthSum fs + PrefixComplexity rs))
            (1 + fs.length)
            (BitString.blen x) := by
        exact stepLogEq_trans hstepEq hrestAdd
      simpa [featureLengthSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        htotal

/-- Theorem 3.6 in paper form:
iterating shortest features with corresponding residual descriptions yields a total description
length `∑ l(fᵢ*) + K(rₛ)` up to `s` logarithmic overhead terms. -/
theorem theorem36_paper {x rs : Program} {fs : List Program}
    (hchain : IsIncrementalPaperCompression x fs rs) :
    StepLogEq (PrefixComplexity x)
      (featureLengthSum fs + PrefixComplexity rs)
      fs.length
      (BitString.blen x) := by
  induction hchain with
  | nil x =>
      simpa using stepLogEq_refl (PrefixComplexity x) (BitString.blen x)
  | @cons x f r rs fs hstep hrest ih =>
      have hstepEq :
          StepLogEq (PrefixComplexity x)
            (BitString.blen f + PrefixComplexity r)
            1
            (BitString.blen x) :=
        stepLogEq_of_paperCompressionStep hstep
      have hrestEq :
          StepLogEq (PrefixComplexity r)
            (featureLengthSum fs + PrefixComplexity rs)
            fs.length
            (BitString.blen x) := by
        exact stepLogEq_of_scale_le ih (residual_length_lt_of_paperCompressionStep hstep).le
      have hrestAdd :
          StepLogEq (BitString.blen f + PrefixComplexity r)
            (BitString.blen f + (featureLengthSum fs + PrefixComplexity rs))
            fs.length
            (BitString.blen x) := by
        exact stepLogEq_add_left hrestEq
      have htotal :
          StepLogEq (PrefixComplexity x)
            (BitString.blen f + (featureLengthSum fs + PrefixComplexity rs))
            (1 + fs.length)
            (BitString.blen x) := by
        exact stepLogEq_trans hstepEq hrestAdd
      simpa [featureLengthSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        htotal

end

end Compression

end IcTheory
