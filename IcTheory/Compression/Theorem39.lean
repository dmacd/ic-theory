import IcTheory.Compression.Theorem38
import IcTheory.Compression.BFeatures
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- Current formalization-level cutoff for terminating the `b`-compressible compression scheme.
It is the natural constant obtained by combining the `b`-feature bound from Theorem 3.7 with the
`|r| ≤ |x| / b` shrinkage built into `b`-descriptive maps. -/
def bCompressionCutoff (b : Nat) : Nat :=
  b * bCompressibleFeatureBound b

/-- One step of the Section 3.5 compression scheme: a shortest `b`-feature together with a
shortest corresponding descriptive map and the resulting residual. -/
structure BCompressionSchemeStep (b : Nat) (x f g r : Program) : Prop where
  shortestFeature : IsShortestBFeature runs b f x
  shortestMap : IsShortestDescriptiveMap runs f g x
  mapRuns : runs g x r
  featureRuns : runs f r x
  compression : CompressionCondition f r x
  residualBound : ResidualBoundByFactor b r x

/-- Inductive model of the Section 3.5 compression scheme. The lists are ordered as
`f₁, ..., fₛ` and `g₁, ..., gₛ`. The scheme stops once the current residual is either small or no
longer `b`-compressible. -/
inductive IsIncrementalBCompressionScheme (b : Nat) :
    Program → List Program → List Program → Program → Prop
  | stop_small (x : Program)
      (hsmall : BitString.blen x ≤ bCompressionCutoff b) :
      IsIncrementalBCompressionScheme b x [] [] x
  | stop_incompressible (x : Program)
      (hnot : ¬ BCompressible b x) :
      IsIncrementalBCompressionScheme b x [] [] x
  | cons {x f g r rs : Program} {fs gs : List Program}
      (hbig : bCompressionCutoff b < BitString.blen x)
      (hbc : BCompressible b x)
      (hstep : BCompressionSchemeStep b x f g r)
      (hrest : IsIncrementalBCompressionScheme b r fs gs rs) :
      IsIncrementalBCompressionScheme b x (f :: fs) (g :: gs) rs

theorem incrementalBCompressionScheme_lengths_eq
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    fs.length = gs.length := by
  induction hchain with
  | stop_small =>
      simp
  | stop_incompressible =>
      simp
  | cons _ _ _ hrest ih =>
      simp [ih]

theorem incrementalBCompressionScheme_terminal
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    BitString.blen rs ≤ bCompressionCutoff b ∨ ¬ BCompressible b rs := by
  induction hchain with
  | stop_small _ hsmall =>
      exact Or.inl hsmall
  | stop_incompressible _ hnot =>
      exact Or.inr hnot
  | cons _ _ _ hrest ih =>
      exact ih

theorem incrementalBCompressionScheme_features_bounded
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    List.Forall (fun f => BitString.blen f ≤ bCompressibleFeatureBound b) fs := by
  induction hchain with
  | stop_small =>
      simp
  | stop_incompressible =>
      simp
  | @cons x f g r rs fs gs hbig hbc hstep hrest ih =>
      have hf :
          BitString.blen f ≤ bCompressibleFeatureBound b := by
        exact theorem37_shortestBFeature hb hbc hstep.shortestFeature
      cases fs with
      | nil =>
          simpa [List.Forall] using hf
      | cons f' fs' =>
          simpa [List.Forall, hf] using ih

theorem incrementalBCompressionScheme_maps_bounded
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    List.Forall
      (fun g => BitString.blen g ≤
        shortFeatureResidualMapBound (bCompressibleFeatureBound b))
      gs := by
  induction hchain with
  | stop_small =>
      simp
  | stop_incompressible =>
      simp
  | @cons x f g r rs fs gs hbig hbc hstep hrest ih =>
      have hf :
          BitString.blen f ≤ bCompressibleFeatureBound b := by
        exact theorem37_shortestBFeature hb hbc hstep.shortestFeature
      have hg :
          BitString.blen g ≤
            shortFeatureResidualMapBound (bCompressibleFeatureBound b) := by
        exact shortestDescriptiveMap_length_le_of_feature_length_le hstep.shortestMap hf
      cases gs with
      | nil =>
          simpa [List.Forall] using hg
      | cons g' gs' =>
          simpa [List.Forall, hg] using ih

private theorem pow_pred_le_length_of_nonemptyScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hfs : fs ≠ []) :
    b ^ (fs.length - 1) ≤ BitString.blen x := by
  induction hchain with
  | stop_small =>
      cases hfs rfl
  | stop_incompressible =>
      cases hfs rfl
  | @cons x f g r rs fs gs hbig hbc hstep hrest ih =>
      cases fs with
      | nil =>
          have hxpos : 0 < BitString.blen x := by
            have hcomp := hstep.compression
            unfold CompressionCondition at hcomp
            omega
          simpa using hxpos
      | cons f' fs' =>
          have hir :
              b ^ ((f' :: fs').length - 1) ≤ BitString.blen r := by
            exact ih (by simp)
          have hrle : BitString.blen r ≤ BitString.blen x / b :=
            hstep.residualBound
          have hpow :
              b ^ ((f :: f' :: fs').length - 1) =
                b * b ^ ((f' :: fs').length - 1) := by
            calc
              b ^ ((f :: f' :: fs').length - 1) = b ^ (List.length (f' :: fs')) := by
                simp
              _ = b ^ (((List.length (f' :: fs')) - 1) + 1) := by
                have hs : ((List.length (f' :: fs')) - 1) + 1 = List.length (f' :: fs') := by
                  simp
                rw [hs]
              _ = b ^ ((List.length (f' :: fs')) - 1) * b := by
                rw [Nat.pow_succ]
              _ = b * b ^ ((List.length (f' :: fs')) - 1) := by
                ac_rfl
          rw [hpow]
          calc
            b * b ^ ((f' :: fs').length - 1) ≤ b * BitString.blen r := by
              exact Nat.mul_le_mul_left b hir
            _ ≤ b * (BitString.blen x / b) := by
              exact Nat.mul_le_mul_left b hrle
            _ ≤ BitString.blen x := by
              exact Nat.mul_div_le (BitString.blen x) b

/-- The number of compression steps in the Section 3.5 scheme is logarithmic in the original
input length. This is the formalization-level replacement for equation (50). -/
theorem incrementalBCompressionScheme_length_le_log
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    fs.length ≤ Nat.log b (BitString.blen x) + 1 := by
  by_cases hfs : fs = []
  · subst hfs
    simp
  · have hpow :
        b ^ (fs.length - 1) ≤ BitString.blen x :=
      pow_pred_le_length_of_nonemptyScheme hchain hfs
    have hxne : BitString.blen x ≠ 0 := by
      apply Nat.ne_of_gt
      exact lt_of_lt_of_le (Nat.pow_pos (Nat.zero_lt_of_lt hb)) hpow
    have hlog : fs.length - 1 ≤ Nat.log b (BitString.blen x) := by
      exact (Nat.le_log_iff_pow_le hb hxne).2 hpow
    omega

/-- Current-form Theorem 3.9: along the `b`-compressible compression scheme, all selected
features and descriptive maps are uniformly bounded by constants depending only on `b`, the step
count is logarithmic in `|x|`, and the terminal residual is either small or no longer
`b`-compressible.

The paper's explicit `l(D_s)` inequality is deferred until the project has a concrete list-based
encoding for the final description object `D_s`. -/
theorem theorem39
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    List.Forall (fun f => BitString.blen f ≤ bCompressibleFeatureBound b) fs ∧
      List.Forall
        (fun g => BitString.blen g ≤
          shortFeatureResidualMapBound (bCompressibleFeatureBound b))
        gs ∧
      fs.length = gs.length ∧
      fs.length ≤ Nat.log b (BitString.blen x) + 1 ∧
      (BitString.blen rs ≤ bCompressionCutoff b ∨ ¬ BCompressible b rs) := by
  refine ⟨incrementalBCompressionScheme_features_bounded hb hchain,
    incrementalBCompressionScheme_maps_bounded hb hchain,
    incrementalBCompressionScheme_lengths_eq hchain,
    incrementalBCompressionScheme_length_le_log hb hchain,
    incrementalBCompressionScheme_terminal hchain⟩

end

end Compression

end IcTheory
