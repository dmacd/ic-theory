import IcTheory.Compression.Theorem38
import IcTheory.Compression.BFeatures
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- Self-delimiting list payload used for the concrete Section 3.5 description object. The list
elements are encoded in order, leaving the final `tail` untouched. -/
def exactProgramListPayload : List Program → Program → Program
  | [], tail => tail
  | f :: fs, tail => BitString.exactPairPayload f (exactProgramListPayload fs tail)

/-- Decode the first `n` entries of an `exactProgramListPayload`, returning the decoded list
and the remaining tail. -/
def decodeProgramListPayload : Nat → Program → List Program × Program
  | 0, payload => ([], payload)
  | n + 1, payload =>
      let headTail := BitString.decodeExactPairPayload payload
      let rest := decodeProgramListPayload n headTail.2
      (headTail.1 :: rest.1, rest.2)

/-- Concrete Section 3.5 description object
`D_s = ⟨s, r_s, f_s, ..., f_1⟩`.

The list `fs` in the scheme is ordered as `f₁, ..., fₛ`, so the stored payload uses
`fs.reverse = [fₛ, ..., f₁]` to match the paper's notation. -/
def schemeDescription (rs : Program) (fs : List Program) : Program :=
  BitString.exactPairPayload
    (BitString.ofNatExact fs.length)
    (BitString.exactPairPayload rs (exactProgramListPayload fs.reverse []))

/-- Pure decoder for `schemeDescription`, exposing the stored step count, terminal residual,
reversed feature list, and leftover tail. -/
def decodeSchemeDescription (payload : Program) : Nat × Program × List Program × Program :=
  let outer := BitString.decodeExactPairPayload payload
  let body := BitString.decodeExactPairPayload outer.2
  let decodedFs := decodeProgramListPayload (BitString.toNatExact outer.1) body.2
  (BitString.toNatExact outer.1, body.1, decodedFs.1, decodedFs.2)

@[simp] theorem decodeProgramListPayload_zero (payload : Program) :
    decodeProgramListPayload 0 payload = ([], payload) := rfl

@[simp] theorem decodeProgramListPayload_succ (n : Nat) (payload : Program) :
    decodeProgramListPayload (n + 1) payload =
      let headTail := BitString.decodeExactPairPayload payload
      let rest := decodeProgramListPayload n headTail.2
      (headTail.1 :: rest.1, rest.2) := rfl

@[simp] theorem decodeProgramListPayload_exactProgramListPayload
    (fs : List Program) (tail : Program) :
    decodeProgramListPayload fs.length (exactProgramListPayload fs tail) = (fs, tail) := by
  induction fs generalizing tail with
  | nil =>
      simp [exactProgramListPayload]
  | cons f fs ih =>
      simp [exactProgramListPayload, ih]

@[simp] theorem decodeSchemeDescription_schemeDescription
    (rs : Program) (fs : List Program) :
    decodeSchemeDescription (schemeDescription rs fs) = (fs.length, rs, fs.reverse, []) := by
  unfold decodeSchemeDescription schemeDescription
  simp
  have hdecode :
      decodeProgramListPayload (fs.reverse.length) (exactProgramListPayload fs.reverse []) =
        (fs.reverse, []) :=
    decodeProgramListPayload_exactProgramListPayload (fs := fs.reverse) (tail := ([] : Program))
  simpa using hdecode

/-- Exact per-feature contribution to the concrete `D_s` encoding, up to the project-standard
binary length bound on the self-delimiting header. -/
def schemeDescriptionFeatureCost (n : Nat) : Nat :=
  n + (2 * BitString.blen (BitString.ofNat n) + 1)

@[simp] theorem exactProgramListPayload_nil (tail : Program) :
    exactProgramListPayload [] tail = tail := rfl

@[simp] theorem exactProgramListPayload_cons (f : Program) (fs : List Program) (tail : Program) :
    exactProgramListPayload (f :: fs) tail =
      BitString.exactPairPayload f (exactProgramListPayload fs tail) := rfl

private theorem exactProgramListPayload_length_le_of_mem_bound
    {fs : List Program} {tail : Program} {n : Nat}
    (hfs : ∀ f ∈ fs, BitString.blen f ≤ n) :
    BitString.blen (exactProgramListPayload fs tail) ≤
      BitString.blen tail + fs.length * schemeDescriptionFeatureCost n := by
  induction fs generalizing tail with
  | nil =>
      simp [exactProgramListPayload, schemeDescriptionFeatureCost]
  | cons f fs ih =>
      have hf : BitString.blen f ≤ n := hfs f (by simp)
      have hrest :
          BitString.blen (exactProgramListPayload fs tail) ≤
            BitString.blen tail + fs.length * schemeDescriptionFeatureCost n := by
        exact ih (fun g hg => hfs g (by simp [hg]))
      have hhead :
          BitString.blen (BitString.ofNatExact (BitString.blen f)) ≤
            BitString.blen (BitString.ofNat n) := by
        exact le_trans
          (BitString.blen_ofNatExact_le_ofNat (BitString.blen f))
          (BitString.blen_ofNat_mono hf)
      calc
        BitString.blen (exactProgramListPayload (f :: fs) tail) =
            BitString.blen f + BitString.blen (exactProgramListPayload fs tail) +
              (2 * BitString.blen (BitString.ofNatExact (BitString.blen f)) + 1) := by
          rw [exactProgramListPayload_cons, BitString.blen_exactPairPayload]
        _ ≤ n + (BitString.blen tail + fs.length * schemeDescriptionFeatureCost n) +
              (2 * BitString.blen (BitString.ofNat n) + 1) := by
          omega
        _ = BitString.blen tail + (f :: fs).length * schemeDescriptionFeatureCost n := by
          simp [schemeDescriptionFeatureCost, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

/-- Explicit length bound for the concrete `D_s` encoding, assuming a uniform bound `n` on all
stored features. -/
theorem schemeDescription_length_le_of_mem_bound
    {rs : Program} {fs : List Program} {n : Nat}
    (hfs : ∀ f ∈ fs, BitString.blen f ≤ n) :
    BitString.blen (schemeDescription rs fs) ≤
      BitString.blen rs +
        fs.length * schemeDescriptionFeatureCost n +
        (2 * BitString.blen (BitString.ofNat (BitString.blen rs)) + 1) +
        (3 * BitString.blen (BitString.ofNat fs.length) + 1) := by
  have hrev :
      ∀ f ∈ fs.reverse, BitString.blen f ≤ n := by
    intro f hf
    exact hfs f ((List.mem_reverse).mp hf)
  have hpayload :
      BitString.blen (exactProgramListPayload fs.reverse []) ≤
        fs.reverse.length * schemeDescriptionFeatureCost n := by
    simpa using
      (exactProgramListPayload_length_le_of_mem_bound
        (fs := fs.reverse) (tail := ([] : Program)) hrev)
  have hrs :
      BitString.blen (BitString.ofNatExact (BitString.blen rs)) ≤
        BitString.blen (BitString.ofNat (BitString.blen rs)) := by
    exact BitString.blen_ofNatExact_le_ofNat (BitString.blen rs)
  have hcount :
      BitString.blen (BitString.ofNatExact fs.length) ≤
        BitString.blen (BitString.ofNat fs.length) := by
    exact BitString.blen_ofNatExact_le_ofNat fs.length
  have hlenBits :
      BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact fs.length))) ≤
        BitString.blen (BitString.ofNat fs.length) := by
    have h₁ :
        BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact fs.length))) ≤
          BitString.blen (BitString.ofNat (BitString.blen (BitString.ofNatExact fs.length))) := by
      exact BitString.blen_ofNatExact_le_ofNat _
    have h₂ :
        BitString.blen (BitString.ofNat (BitString.blen (BitString.ofNatExact fs.length))) ≤
          BitString.blen (BitString.ofNat fs.length) := by
      refine le_trans (BitString.blen_ofNat_le_self _) ?_
      exact BitString.blen_ofNatExact_le_ofNat fs.length
    exact le_trans h₁ h₂
  unfold schemeDescription
  rw [BitString.blen_exactPairPayload, BitString.blen_exactPairPayload]
  simp at hpayload
  omega

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

/-- Concrete size bound for the Section 3.5 description object `D_s = ⟨s, r_s, f_s, ..., f_1⟩`.

This packages the exact self-delimiting encoding length in terms of the terminal residual, the
uniform per-feature constant from Theorem 3.7, and the logarithmic step-count bound. -/
theorem schemeDescription_length_le_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    BitString.blen (schemeDescription rs fs) ≤
      BitString.blen rs +
        (Nat.log b (BitString.blen x) + 1) *
          schemeDescriptionFeatureCost (bCompressibleFeatureBound b) +
        (2 * BitString.blen (BitString.ofNat (BitString.blen rs)) + 1) +
        (3 * BitString.blen (BitString.ofNat (Nat.log b (BitString.blen x) + 1)) + 1) := by
  have hfs :
      ∀ f ∈ fs, BitString.blen f ≤ bCompressibleFeatureBound b := by
    intro f hf
    have hall := incrementalBCompressionScheme_features_bounded hb hchain
    exact (List.forall_iff_forall_mem.mp hall) f hf
  have hbase :
      BitString.blen (schemeDescription rs fs) ≤
        BitString.blen rs +
          fs.length * schemeDescriptionFeatureCost (bCompressibleFeatureBound b) +
          (2 * BitString.blen (BitString.ofNat (BitString.blen rs)) + 1) +
          (3 * BitString.blen (BitString.ofNat fs.length) + 1) := by
    exact schemeDescription_length_le_of_mem_bound hfs
  have hlen : fs.length ≤ Nat.log b (BitString.blen x) + 1 :=
    incrementalBCompressionScheme_length_le_log hb hchain
  have hmono :
      BitString.blen (BitString.ofNat fs.length) ≤
        BitString.blen (BitString.ofNat (Nat.log b (BitString.blen x) + 1)) := by
    exact BitString.blen_ofNat_mono hlen
  have hmul :
      fs.length * schemeDescriptionFeatureCost (bCompressibleFeatureBound b) ≤
        (Nat.log b (BitString.blen x) + 1) *
          schemeDescriptionFeatureCost (bCompressibleFeatureBound b) := by
    exact Nat.mul_le_mul_right _ hlen
  have hhead :
      3 * BitString.blen (BitString.ofNat fs.length) + 1 ≤
        3 * BitString.blen (BitString.ofNat (Nat.log b (BitString.blen x) + 1)) + 1 := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 hmono) 1
  exact le_trans hbase <| by omega

/-- Current-form Theorem 3.9: along the `b`-compressible compression scheme, all selected
features and descriptive maps are uniformly bounded by constants depending only on `b`, the step
count is logarithmic in `|x|`, and the terminal residual is either small or no longer
`b`-compressible. The concrete description object `D_s = ⟨s, r_s, f_s, ..., f_1⟩` is now encoded
as `schemeDescription rs fs`, with its length bounded explicitly in the companion theorem
`schemeDescription_length_le_of_incrementalBCompressionScheme`. -/
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
