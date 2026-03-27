import IcTheory.Compression.Theorem38
import IcTheory.Compression.BFeatures
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

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

/-- Formalization-level version of equation (51): once all stored features are bounded by a
uniform constant `n`, the concrete description object `D_s` differs from the terminal residual
length by only logarithmic headers and a linear-in-steps constant term. -/
theorem schemeDescription_logLe_terminalResidual_of_mem_bound
    {rs : Program} {fs : List Program} {n : Nat}
    (hfs : ∀ f ∈ fs, BitString.blen f ≤ n) :
    LogLe (BitString.blen (schemeDescription rs fs))
      (BitString.blen rs + fs.length * schemeDescriptionFeatureCost n)
      (max (BitString.blen rs) fs.length) := by
  have hlen := schemeDescription_length_le_of_mem_bound (rs := rs) (fs := fs) (n := n) hfs
  have hrsLog :
      BitString.blen (BitString.ofNat (BitString.blen rs)) ≤
        logPenalty (max (BitString.blen rs) fs.length) + 1 := by
    have hmono :
        logPenalty (BitString.blen rs) ≤ logPenalty (max (BitString.blen rs) fs.length) :=
      logPenalty_mono (Nat.le_max_left _ _)
    have hsize := blen_ofNat_le_logPenalty_succ (BitString.blen rs)
    omega
  have hstepsLog :
      BitString.blen (BitString.ofNat fs.length) ≤
        logPenalty (max (BitString.blen rs) fs.length) + 1 := by
    have hmono :
        logPenalty fs.length ≤ logPenalty (max (BitString.blen rs) fs.length) :=
      logPenalty_mono (Nat.le_max_right _ _)
    have hsize := blen_ofNat_le_logPenalty_succ fs.length
    omega
  refine ⟨5, 7, ?_⟩
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

/-- Semantic execution of the stored feature list in a concrete description object. The list is
run left-to-right, starting from the terminal residual. -/
inductive RunsStoredProgramList : List Program → Program → Program → Prop
  | nil (r : Program) :
      RunsStoredProgramList [] r r
  | cons {f r y x : Program} {fs : List Program}
      (hf : runs f r y)
      (hrest : RunsStoredProgramList fs y x) :
      RunsStoredProgramList (f :: fs) r x

private theorem runsStoredProgramList_snoc
    {fs : List Program} {r y x f : Program}
    (hfs : RunsStoredProgramList fs r y)
    (hf : runs f y x) :
    RunsStoredProgramList (fs ++ [f]) r x := by
  induction hfs generalizing x f with
  | nil =>
      simpa using RunsStoredProgramList.cons hf (RunsStoredProgramList.nil x)
  | @cons g r z y gs hg hrest ih =>
      simpa [List.cons_append] using RunsStoredProgramList.cons hg (ih hf)

/-- The stored feature list in `schemeDescription rs fs` really reconstructs `x` from `rs`. -/
theorem runsStoredProgramList_reverse_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    RunsStoredProgramList fs.reverse rs x := by
  induction hchain with
  | stop_small x _ =>
      simpa using RunsStoredProgramList.nil x
  | stop_incompressible x _ =>
      simpa using RunsStoredProgramList.nil x
  | @cons x f g r rs fs gs _ _ hstep _ ih =>
      simpa using runsStoredProgramList_snoc ih hstep.featureRuns

/-- Helper: the concrete description object with the stored feature order exposed directly. -/
def storedSchemeDescription (rs : Program) (storedFs : List Program) : Program :=
  BitString.exactPairPayload
    (BitString.ofNatExact storedFs.length)
    (BitString.exactPairPayload rs (exactProgramListPayload storedFs []))

@[simp] theorem schemeDescription_eq_storedSchemeDescription (rs : Program) (fs : List Program) :
    schemeDescription rs fs = storedSchemeDescription rs fs.reverse := by
  simp [schemeDescription, storedSchemeDescription]

private def storedSchemeOuterDecoded (n : Nat) : Program × Program :=
  BitString.decodeExactPairPayload (BitString.ofNatExact n)

private theorem storedSchemeOuterDecoded_computable : Computable storedSchemeOuterDecoded := by
  exact BitString.decodeExactPairPayload_computable.comp
    (BitString.ofNatExact_computable.comp Computable.id)

private def storedSchemeStepCountNat (n : Nat) : Nat :=
  BitString.toNatExact (storedSchemeOuterDecoded n).1

private theorem storedSchemeStepCountNat_computable : Computable storedSchemeStepCountNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.fst.comp storedSchemeOuterDecoded_computable)

private def storedSchemeBodyDecoded (n : Nat) : Program × Program :=
  BitString.decodeExactPairPayload (storedSchemeOuterDecoded n).2

private theorem storedSchemeBodyDecoded_computable : Computable storedSchemeBodyDecoded := by
  exact BitString.decodeExactPairPayload_computable.comp
    (Computable.snd.comp storedSchemeOuterDecoded_computable)

private def storedSchemeInitialState (n : Nat) : Nat × Nat :=
  (BitString.toNatExact (storedSchemeBodyDecoded n).1,
    BitString.toNatExact (storedSchemeBodyDecoded n).2)

private theorem storedSchemeInitialState_computable : Computable storedSchemeInitialState := by
  exact Computable.pair
    (BitString.toNatExact_computable.comp
      (Computable.fst.comp storedSchemeBodyDecoded_computable))
    (BitString.toNatExact_computable.comp
      (Computable.snd.comp storedSchemeBodyDecoded_computable))

private def storedSchemeStepDecoded (state : Nat × Nat) : Program × Program :=
  BitString.decodeExactPairPayload (BitString.ofNatExact state.2)

private theorem storedSchemeStepDecoded_computable : Computable storedSchemeStepDecoded := by
  exact BitString.decodeExactPairPayload_computable.comp
    (BitString.ofNatExact_computable.comp Computable.snd)

private def storedSchemeStepCodeNat (state : Nat × Nat) : Nat :=
  BitString.toNatExact (storedSchemeStepDecoded state).1

private theorem storedSchemeStepCodeNat_computable : Computable storedSchemeStepCodeNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.fst.comp storedSchemeStepDecoded_computable)

private def storedSchemeStepRestPayloadNat (state : Nat × Nat) : Nat :=
  BitString.toNatExact (storedSchemeStepDecoded state).2

private theorem storedSchemeStepRestPayloadNat_computable :
    Computable storedSchemeStepRestPayloadNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.snd.comp storedSchemeStepDecoded_computable)

/-- One machine step of the `D_s` interpreter: decode the next stored feature from the payload,
run it on the current string, and update the residual payload. -/
private def storedSchemeStepPart (state : Nat × Nat) : Part (Nat × Nat) :=
  (Code.eval (Denumerable.ofNat Code (storedSchemeStepCodeNat state)) state.1).map
    (fun nextNat => (nextNat, storedSchemeStepRestPayloadNat state))

/-- Pure loop used by the concrete `D_s` interpreter. -/
private def storedSchemeLoop : Nat → Nat × Nat → Part (Nat × Nat)
  | 0, state => Part.some state
  | n + 1, state => (storedSchemeLoop n state).bind storedSchemeStepPart

private theorem storedSchemeExecStepState_partrec :
    _root_.Partrec fun q : Nat × (Nat × Nat) =>
      (Code.eval (Denumerable.ofNat Code (storedSchemeStepCodeNat q.2)) q.2.1).map
        (fun nextNat => (nextNat, storedSchemeStepRestPayloadNat q.2)) := by
  have hCode : Computable fun q : Nat × (Nat × Nat) =>
      Denumerable.ofNat Code (storedSchemeStepCodeNat q.2) := by
    exact (Computable.ofNat Code).comp
      (storedSchemeStepCodeNat_computable.comp Computable.snd)
  have hInput : Computable fun q : Nat × (Nat × Nat) => q.2.1 := by
    exact Computable.fst.comp Computable.snd
  have hEval : _root_.Partrec fun q : Nat × (Nat × Nat) =>
      Code.eval (Denumerable.ofNat Code (storedSchemeStepCodeNat q.2)) q.2.1 := by
    exact Code.eval_part.comp hCode hInput
  have hOut : Computable₂
      (fun (q : Nat × (Nat × Nat)) (nextNat : Nat) =>
        (nextNat, storedSchemeStepRestPayloadNat q.2)) := by
    exact (Computable.pair Computable.snd
      (storedSchemeStepRestPayloadNat_computable.comp
        (Computable.snd.comp Computable.fst))).to₂
  exact _root_.Partrec.map hEval hOut

private theorem storedSchemeExecStep_partrec :
    _root_.Partrec₂ fun (_ : Nat) (q : Nat × (Nat × Nat)) =>
      (Code.eval (Denumerable.ofNat Code (storedSchemeStepCodeNat q.2)) q.2.1).map
        (fun nextNat => (nextNat, storedSchemeStepRestPayloadNat q.2)) := by
  simpa using (storedSchemeExecStepState_partrec.comp Computable.snd).to₂

private theorem storedSchemeLoop_eq_natRec (count : Nat) (state : Nat × Nat) :
    storedSchemeLoop count state =
      Nat.rec (Part.some state)
        (fun _ IH => IH.bind fun st =>
          (Code.eval (Denumerable.ofNat Code (storedSchemeStepCodeNat st)) st.1).map
            (fun nextNat => (nextNat, storedSchemeStepRestPayloadNat st)))
        count := by
  induction count generalizing state with
  | zero =>
      simp [storedSchemeLoop]
  | succ count ih =>
      rw [storedSchemeLoop, ih]
      rfl

private theorem storedSchemeInterpreterNat_partrec :
    Nat.Partrec fun n =>
      Part.map Prod.fst (storedSchemeLoop (storedSchemeStepCountNat n) (storedSchemeInitialState n)) := by
  have hBase : _root_.Partrec fun n : Nat => Part.some (storedSchemeInitialState n) := by
    exact storedSchemeInitialState_computable.partrec
  have hLoop : _root_.Partrec fun n : Nat =>
      Nat.rec (Part.some (storedSchemeInitialState n))
        (fun _ IH => IH.bind fun st =>
          (Code.eval (Denumerable.ofNat Code (storedSchemeStepCodeNat st)) st.1).map
            (fun nextNat => (nextNat, storedSchemeStepRestPayloadNat st)))
        (storedSchemeStepCountNat n) := by
    exact _root_.Partrec.nat_rec storedSchemeStepCountNat_computable hBase
      storedSchemeExecStep_partrec
  have hFst : Computable₂ fun (_ : Nat) (st : Nat × Nat) => st.1 := by
    exact (Computable.fst.comp Computable.snd).to₂
  have hMap : _root_.Partrec fun n =>
      Part.map Prod.fst
        (Nat.rec (Part.some (storedSchemeInitialState n))
        (fun _ IH => IH.bind fun st =>
          (Code.eval (Denumerable.ofNat Code (storedSchemeStepCodeNat st)) st.1).map
            (fun nextNat => (nextNat, storedSchemeStepRestPayloadNat st)))
        (storedSchemeStepCountNat n)) := by
    exact _root_.Partrec.map hLoop hFst
  refine _root_.Partrec.nat_iff.1 ?_
  exact hMap.of_eq fun n => by
    simp [storedSchemeLoop_eq_natRec]

theorem exists_storedSchemeInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n =
        (storedSchemeLoop (storedSchemeStepCountNat n) (storedSchemeInitialState n)).map Prod.fst := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 storedSchemeInterpreterNat_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- Fixed machine `V` for the concrete description object `D_s`. It decodes
`⟨s, r_s, f_s, ..., f_1⟩` and iteratively reconstructs the original string. -/
noncomputable def storedSchemeInterpreterCode : Code :=
  Classical.choose exists_storedSchemeInterpreterCode

theorem eval_storedSchemeInterpreterCode (n : Nat) :
    Code.eval storedSchemeInterpreterCode n =
      (storedSchemeLoop (storedSchemeStepCountNat n) (storedSchemeInitialState n)).map Prod.fst :=
  Classical.choose_spec exists_storedSchemeInterpreterCode n

/-- Plain interpreter implementing the machine `V` from Section 3.5. -/
noncomputable def schemeDescriptionInterpreter : Program :=
  codeToProgram storedSchemeInterpreterCode

/-- Constant overhead contributed by the fixed plain Section 3.5 interpreter itself. -/
noncomputable def schemeDescriptionInterpreterOverhead : Nat :=
  2 * BitString.blen schemeDescriptionInterpreter + 2

theorem evalSchemeDescriptionPrefixPacked_partrec :
    Nat.Partrec fun n =>
      Code.eval storedSchemeInterpreterCode n.unpair.2 := by
  have hsnd : Computable₂ (fun a b : ℕ => b) := Computable₂.mk Computable.snd
  have hcode : Computable₂ (fun _ _ : ℕ => storedSchemeInterpreterCode) := by
    exact Computable₂.mk (Computable.const storedSchemeInterpreterCode)
  have hEval : Partrec₂ (fun a b : ℕ => Code.eval storedSchemeInterpreterCode b) := by
    exact Code.eval_part.comp₂ hcode hsnd
  simpa [Nat.unpaired] using (Partrec₂.unpaired'.2 hEval)

theorem exists_schemeDescriptionPrefixInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n = Code.eval storedSchemeInterpreterCode n.unpair.2 := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalSchemeDescriptionPrefixPacked_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- Fixed prefix wrapper for `schemeDescriptionInterpreter`: it ignores the outer conditioning
input and feeds the payload directly to the plain machine `V`. -/
noncomputable def schemeDescriptionPrefixInterpreterCode : Code :=
  Classical.choose exists_schemeDescriptionPrefixInterpreterCode

theorem eval_schemeDescriptionPrefixInterpreterCode (n : Nat) :
    Code.eval schemeDescriptionPrefixInterpreterCode n =
      Code.eval storedSchemeInterpreterCode n.unpair.2 :=
  Classical.choose_spec exists_schemeDescriptionPrefixInterpreterCode n

/-- Prefix interpreter witnessing that the concrete description object `D_s` is also a prefix
description up to logarithmic self-delimiting overhead. -/
noncomputable def schemeDescriptionPrefixInterpreter : Program :=
  codeToProgram schemeDescriptionPrefixInterpreterCode

/-- Constant overhead contributed by the fixed Section 3.5 prefix wrapper. -/
noncomputable def schemeDescriptionPrefixOverhead : Nat :=
  2 * BitString.blen schemeDescriptionPrefixInterpreter + 2

@[simp] theorem runs_schemeDescriptionPrefixInterpreter_iff
    (input payload output : BitString) :
    runs schemeDescriptionPrefixInterpreter (packedInput input payload) output ↔
      runs schemeDescriptionInterpreter payload output := by
  rw [schemeDescriptionPrefixInterpreter, runs_codeToProgram_iff]
  rw [schemeDescriptionInterpreter, runs_codeToProgram_iff]
  simp [packedInput, runs, programToCode, eval_schemeDescriptionPrefixInterpreterCode]

private def executeStoredProgramListNat : List Program → Nat → Part Nat
  | [], currentNat => Part.some currentNat
  | f :: fs, currentNat =>
      Code.eval (programToCode f) currentNat >>= executeStoredProgramListNat fs

private theorem executeStoredProgramListNat_append_singleton
    (storedFs : List Program) (f : Program) (currentNat : Nat) :
    executeStoredProgramListNat (storedFs ++ [f]) currentNat =
      executeStoredProgramListNat storedFs currentNat >>= fun nextNat =>
        Code.eval (programToCode f) nextNat := by
  induction storedFs generalizing currentNat with
  | nil =>
      simp [executeStoredProgramListNat]
  | cons g gs ih =>
      simp [executeStoredProgramListNat, Part.bind_assoc]
      refine congrArg (Part.bind ((programToCode g).eval currentNat)) ?_
      funext nextNat
      exact ih nextNat

@[simp] private theorem storedSchemeStepCountNat_storedSchemeDescription
    (rs : Program) (storedFs : List Program) :
    storedSchemeStepCountNat (BitString.toNatExact (storedSchemeDescription rs storedFs)) =
      storedFs.length := by
  simp [storedSchemeStepCountNat, storedSchemeDescription, storedSchemeOuterDecoded]

@[simp] private theorem storedSchemeInitialState_storedSchemeDescription
    (rs : Program) (storedFs : List Program) :
    storedSchemeInitialState (BitString.toNatExact (storedSchemeDescription rs storedFs)) =
      (BitString.toNatExact rs, BitString.toNatExact (exactProgramListPayload storedFs [])) := by
  simp [storedSchemeInitialState, storedSchemeDescription, storedSchemeBodyDecoded,
    storedSchemeOuterDecoded]

@[simp] private theorem storedSchemeStepPart_exactProgramListPayload
    (currentNat : Nat) (f : Program) (suffix : List Program) :
    storedSchemeStepPart
        (currentNat, BitString.toNatExact (exactProgramListPayload (f :: suffix) [])) =
      (Code.eval (programToCode f) currentNat).map
        (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload suffix []))) := by
  simp [storedSchemeStepPart, storedSchemeStepCodeNat, storedSchemeStepRestPayloadNat,
    storedSchemeStepDecoded, exactProgramListPayload, programToCode]

private theorem storedSchemeLoop_exactProgramListPayload_append
    (storedFs suffix : List Program) (currentNat : Nat) :
    storedSchemeLoop storedFs.length
        (currentNat, BitString.toNatExact (exactProgramListPayload (storedFs ++ suffix) [])) =
      (executeStoredProgramListNat storedFs currentNat).map
        (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload suffix []))) := by
  induction storedFs using List.reverseRecOn generalizing currentNat suffix with
  | nil =>
      simp [storedSchemeLoop, executeStoredProgramListNat]
  | append_singleton storedFs f ih =>
      calc
        storedSchemeLoop (List.length (storedFs ++ [f]))
            (currentNat, BitString.toNatExact (exactProgramListPayload ((storedFs ++ [f]) ++ suffix) [])) =
          (storedSchemeLoop storedFs.length
            (currentNat, BitString.toNatExact (exactProgramListPayload (storedFs ++ (f :: suffix)) []))).bind
              storedSchemeStepPart := by
                simp [storedSchemeLoop]
        _ =
          ((executeStoredProgramListNat storedFs currentNat).map
            (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload (f :: suffix) [])))).bind
              storedSchemeStepPart := by
                rw [ih (f :: suffix) currentNat]
        _ =
          (executeStoredProgramListNat (storedFs ++ [f]) currentNat).map
            (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload suffix []))) := by
          calc
            ((executeStoredProgramListNat storedFs currentNat).map
                (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload (f :: suffix) [])))).bind
                storedSchemeStepPart =
              (executeStoredProgramListNat storedFs currentNat).bind
                (fun y => storedSchemeStepPart
                  (y, BitString.toNatExact (exactProgramListPayload (f :: suffix) []))) := by
                rw [Part.bind_map]
            _ =
              (executeStoredProgramListNat storedFs currentNat).bind
                (fun y =>
                  Part.map (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload suffix [])))
                    ((programToCode f).eval y)) := by
                refine congrArg (Part.bind (executeStoredProgramListNat storedFs currentNat)) ?_
                funext y
                simpa [exactProgramListPayload] using
                  (storedSchemeStepPart_exactProgramListPayload y f suffix)
            _ =
              Part.map (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload suffix [])))
                ((executeStoredProgramListNat storedFs currentNat).bind
                  fun nextNat => (programToCode f).eval nextNat) := by
                rw [Part.map_bind]
            _ =
              (executeStoredProgramListNat (storedFs ++ [f]) currentNat).map
                (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload suffix []))) := by
                exact congrArg
                  (Part.map
                    (fun nextNat => (nextNat, BitString.toNatExact (exactProgramListPayload suffix []))))
                  (executeStoredProgramListNat_append_singleton storedFs f currentNat).symm

private theorem executeStoredProgramListNat_of_runsStoredProgramList
    {storedFs : List Program} {r x : Program}
    (hchain : RunsStoredProgramList storedFs r x) :
    executeStoredProgramListNat storedFs (BitString.toNatExact r) =
      Part.some (BitString.toNatExact x) := by
  induction hchain with
  | nil r =>
      simp [executeStoredProgramListNat]
  | @cons f r y x fs hf hrest ih =>
      rw [executeStoredProgramListNat]
      have hf' : Code.eval (programToCode f) (BitString.toNatExact r) =
          Part.some (BitString.toNatExact y) := by
        simpa [runs] using hf
      rw [hf']
      simpa using ih

/-- Concrete correctness of the Section 3.5 interpreter on any stored feature list. -/
theorem schemeDescriptionInterpreter_runs_of_storedPrograms
    {storedFs : List Program} {r x : Program}
    (hchain : RunsStoredProgramList storedFs r x) :
    runs schemeDescriptionInterpreter (storedSchemeDescription r storedFs) x := by
  rw [schemeDescriptionInterpreter, runs_codeToProgram_iff]
  rw [eval_storedSchemeInterpreterCode]
  rw [storedSchemeStepCountNat_storedSchemeDescription, storedSchemeInitialState_storedSchemeDescription]
  have hloop :
      storedSchemeLoop storedFs.length
          (BitString.toNatExact r, BitString.toNatExact (exactProgramListPayload storedFs [])) =
        (executeStoredProgramListNat storedFs (BitString.toNatExact r)).map
          (fun nextNat => (nextNat, 0)) := by
    simpa using storedSchemeLoop_exactProgramListPayload_append storedFs [] (BitString.toNatExact r)
  rw [hloop, executeStoredProgramListNat_of_runsStoredProgramList hchain]
  simp

/-- The concrete Section 3.5 description object really reconstructs the original string. -/
theorem schemeDescriptionInterpreter_runs_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    runs schemeDescriptionInterpreter (schemeDescription rs fs) x := by
  simpa [schemeDescription_eq_storedSchemeDescription] using
    schemeDescriptionInterpreter_runs_of_storedPrograms
      (runsStoredProgramList_reverse_of_incrementalBCompressionScheme hchain)

theorem prefixRuns_schemeDescription_of_runs
    {input ds x : Program}
    (hruns : runs schemeDescriptionInterpreter ds x) :
    PrefixRuns (BitString.pair schemeDescriptionPrefixInterpreter (BitString.e2 ds)) input x := by
  refine ⟨schemeDescriptionPrefixInterpreter, ds, rfl, ?_⟩
  simpa using (runs_schemeDescriptionPrefixInterpreter_iff input ds x).2 hruns

theorem prefixConditionalComplexity_le_schemeDescription
    {input ds x : Program}
    (hruns : runs schemeDescriptionInterpreter ds x) :
    PrefixConditionalComplexity x input ≤
      BitString.blen (BitString.pair schemeDescriptionPrefixInterpreter (BitString.e2 ds)) := by
  exact prefixConditionalComplexity_le_length (prefixRuns_schemeDescription_of_runs hruns)

theorem prefixComplexity_le_schemeDescriptionLength
    {ds x : Program}
    (hruns : runs schemeDescriptionInterpreter ds x) :
    PrefixComplexity x ≤
      BitString.blen ds +
        2 * BitString.blen (BitString.ofNat (BitString.blen ds)) +
        schemeDescriptionPrefixOverhead := by
  have h := prefixConditionalComplexity_le_schemeDescription (input := ([] : Program)) hruns
  rw [BitString.blen_pair, BitString.blen_e2] at h
  unfold PrefixComplexity schemeDescriptionPrefixOverhead at *
  omega

/-- The concrete Section 3.5 description object itself yields a prefix witness for `x`, with only
the usual logarithmic self-delimiting overhead beyond `|D_s|`. -/
theorem prefixComplexity_le_schemeDescription_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    PrefixComplexity x ≤
      BitString.blen (schemeDescription rs fs) +
        2 * BitString.blen (BitString.ofNat (BitString.blen (schemeDescription rs fs))) +
        schemeDescriptionPrefixOverhead := by
  exact prefixComplexity_le_schemeDescriptionLength
    (schemeDescriptionInterpreter_runs_of_incrementalBCompressionScheme hchain)

/-- Packaged version of the Section 3.5 prefix bound using the explicit size estimate for
`schemeDescription rs fs`. -/
theorem prefixComplexity_le_schemeDescriptionBound_of_incrementalBCompressionScheme
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    PrefixComplexity x ≤
      let n :=
        BitString.blen rs +
        (Nat.log b (BitString.blen x) + 1) *
            schemeDescriptionFeatureCost (bCompressibleFeatureBound b) +
          (2 * BitString.blen (BitString.ofNat (BitString.blen rs)) + 1) +
          (3 * BitString.blen (BitString.ofNat (Nat.log b (BitString.blen x) + 1)) + 1)
      n + 2 * BitString.blen (BitString.ofNat n) + schemeDescriptionPrefixOverhead := by
  let n :=
    BitString.blen rs +
    (Nat.log b (BitString.blen x) + 1) *
        schemeDescriptionFeatureCost (bCompressibleFeatureBound b) +
      (2 * BitString.blen (BitString.ofNat (BitString.blen rs)) + 1) +
      (3 * BitString.blen (BitString.ofNat (Nat.log b (BitString.blen x) + 1)) + 1)
  have hprefix := prefixComplexity_le_schemeDescription_of_incrementalBCompressionScheme hchain
  have hlen : BitString.blen (schemeDescription rs fs) ≤ n := by
    simpa [n] using schemeDescription_length_le_of_incrementalBCompressionScheme hb hchain
  have hmono :
      BitString.blen (BitString.ofNat (BitString.blen (schemeDescription rs fs))) ≤
        BitString.blen (BitString.ofNat n) := by
    exact BitString.blen_ofNat_mono hlen
  have hbound :
      BitString.blen (schemeDescription rs fs) +
            2 * BitString.blen (BitString.ofNat (BitString.blen (schemeDescription rs fs))) +
          schemeDescriptionPrefixOverhead ≤
        n + 2 * BitString.blen (BitString.ofNat n) + schemeDescriptionPrefixOverhead := by
    exact Nat.add_le_add_right
      (Nat.add_le_add hlen (Nat.mul_le_mul_left 2 hmono))
      schemeDescriptionPrefixOverhead
  exact le_trans hprefix hbound

/-- Current prefix-form replacement for the lower side of equation (48): the concrete description
object `D_s` gives a prefix description of `x` up to the expected self-delimiting overhead. -/
theorem theorem39_eq48_lower_current
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    LogLe (PrefixComplexity x)
      (BitString.blen (schemeDescription rs fs))
      (BitString.blen (schemeDescription rs fs)) := by
  have hprefix := prefixComplexity_le_schemeDescription_of_incrementalBCompressionScheme hchain
  have hlog :
      BitString.blen (BitString.ofNat (BitString.blen (schemeDescription rs fs))) ≤
        logPenalty (BitString.blen (schemeDescription rs fs)) + 1 := by
    simpa using
      blen_ofNat_le_logPenalty_succ (BitString.blen (schemeDescription rs fs))
  refine ⟨2, schemeDescriptionPrefixOverhead + 2, ?_⟩
  omega

/-- Explicit upper bound on the concrete description object `D_s` at the scheme scale. This is
the current formalization-level upper side of equation (48). -/
theorem theorem39_eq48_upper_current
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    BitString.blen (schemeDescription rs fs) ≤
      BitString.blen rs +
        (Nat.log b (BitString.blen x) + 1) *
          schemeDescriptionFeatureCost (bCompressibleFeatureBound b) +
        (2 * BitString.blen (BitString.ofNat (BitString.blen rs)) + 1) +
        (3 * BitString.blen (BitString.ofNat (Nat.log b (BitString.blen x) + 1)) + 1) := by
  exact schemeDescription_length_le_of_incrementalBCompressionScheme hb hchain

/-- Equation (49): every selected feature in the Section 3.5 scheme has uniformly bounded length,
with a constant depending only on `b`. -/
theorem theorem39_eq49
    {b : Nat} {x rs : Program} {fs gs : List Program} {f : Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs)
    (hf : f ∈ fs) :
    BitString.blen f ≤ bCompressibleFeatureBound b := by
  exact (List.forall_iff_forall_mem.mp
    (incrementalBCompressionScheme_features_bounded hb hchain)) f hf

/-- Equation (50): the number of steps in the Section 3.5 scheme is logarithmic in `|x|`. -/
theorem theorem39_eq50
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    fs.length ≤ Nat.log b (BitString.blen x) + 1 := by
  exact incrementalBCompressionScheme_length_le_log hb hchain

/-- Formalization-level version of equation (51) specialized to the Section 3.5 scheme. -/
theorem theorem39_eq51
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    LogLe (BitString.blen (schemeDescription rs fs))
      (BitString.blen rs +
        fs.length * schemeDescriptionFeatureCost (bCompressibleFeatureBound b))
      (max (BitString.blen rs) fs.length) := by
  have hfs :
      ∀ f ∈ fs, BitString.blen f ≤ bCompressibleFeatureBound b := by
    intro f hf
    exact theorem39_eq49 hb hchain hf
  exact schemeDescription_logLe_terminalResidual_of_mem_bound hfs

/-- Current-form Theorem 3.9: the concrete description object `D_s = ⟨s, r_s, f_s, ..., f_1⟩`
now has explicit lower and upper prefix-complexity bounds, its raw length satisfies the
formalization-level version of equation (51), all selected features and descriptive maps are
uniformly bounded by constants depending only on `b`, the step count is logarithmic in `|x|`,
and the terminal residual is either small or no longer `b`-compressible. -/
theorem theorem39
    {b : Nat} {x rs : Program} {fs gs : List Program}
    (hb : 1 < b)
    (hchain : IsIncrementalBCompressionScheme b x fs gs rs) :
    LogLe (PrefixComplexity x)
      (BitString.blen (schemeDescription rs fs))
      (BitString.blen (schemeDescription rs fs)) ∧
      LogLe (BitString.blen (schemeDescription rs fs))
        (BitString.blen rs +
          fs.length * schemeDescriptionFeatureCost (bCompressibleFeatureBound b))
        (max (BitString.blen rs) fs.length) ∧
      List.Forall (fun f => BitString.blen f ≤ bCompressibleFeatureBound b) fs ∧
      List.Forall
        (fun g => BitString.blen g ≤
          shortFeatureResidualMapBound (bCompressibleFeatureBound b))
        gs ∧
      fs.length = gs.length ∧
      fs.length ≤ Nat.log b (BitString.blen x) + 1 ∧
      (BitString.blen rs ≤ bCompressionCutoff b ∨ ¬ BCompressible b rs) := by
  refine ⟨theorem39_eq48_lower_current hchain,
    theorem39_eq51 hb hchain,
    incrementalBCompressionScheme_features_bounded hb hchain,
    incrementalBCompressionScheme_maps_bounded hb hchain,
    incrementalBCompressionScheme_lengths_eq hchain,
    theorem39_eq50 hb hchain,
    incrementalBCompressionScheme_terminal hchain⟩

end

end Compression

end IcTheory
