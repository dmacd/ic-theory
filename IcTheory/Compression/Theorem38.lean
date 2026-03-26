import IcTheory.Compression.Theorem37
import IcTheory.Computability.FinitePrefixDescriptions
import IcTheory.Computability.PrefixInformation
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

private theorem featureResidualMapNat_partrec (f : Program) :
    Nat.Partrec fun inputNat =>
      (Code.eval (programToCode featureResidualPairSearcher)
        (Nat.pair (BitString.toNatExact f) inputNat)).map
          (fun pairNat : Nat => pairNat.unpair.1) := by
  have hCode : Computable fun _ : Nat => programToCode featureResidualPairSearcher := by
    exact Computable.const (programToCode featureResidualPairSearcher)
  have hInput : Computable fun inputNat : Nat => Nat.pair (BitString.toNatExact f) inputNat := by
    exact (Primrec₂.natPair.to_comp).comp
      (Computable.const (BitString.toNatExact f))
      Computable.id
  have hEval : _root_.Partrec fun inputNat =>
      Code.eval (programToCode featureResidualPairSearcher)
        (Nat.pair (BitString.toNatExact f) inputNat) := by
    exact Code.eval_part.comp hCode hInput
  have hLeft : Computable₂ (fun _ pairNat : Nat => pairNat.unpair.1) := by
    exact Computable₂.mk <|
      Computable.fst.comp (Computable.unpair.comp Computable.snd)
  exact _root_.Partrec.nat_iff.1 (_root_.Partrec.map hEval hLeft)

private theorem exists_featureResidualMapCode (f : Program) :
    ∃ c : Code, ∀ inputNat : Nat,
      Code.eval c inputNat =
        (Code.eval (programToCode featureResidualPairSearcher)
          (Nat.pair (BitString.toNatExact f) inputNat)).map
            (fun pairNat : Nat => pairNat.unpair.1) := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 (featureResidualMapNat_partrec f)
  exact ⟨c, fun inputNat => by simpa using congrFun hc inputNat⟩

/-- Plain residual-map program obtained by fixing a feature `f`, running the canonical residual
searcher on `⟨f, x⟩`, and projecting out the residual component. -/
noncomputable def featureResidualMapProgram (f : Program) : Program :=
  codeToProgram (Classical.choose (exists_featureResidualMapCode f))

private theorem eval_featureResidualMapCode (f : Program) (inputNat : Nat) :
    Code.eval (Classical.choose (exists_featureResidualMapCode f)) inputNat =
      (Code.eval (programToCode featureResidualPairSearcher)
        (Nat.pair (BitString.toNatExact f) inputNat)).map
          (fun pairNat : Nat => pairNat.unpair.1) :=
  Classical.choose_spec (exists_featureResidualMapCode f) inputNat

theorem featureResidualMapProgram_runs_of_feature {f x : Program}
    (hfeature : IsFeature runs f x) :
    ∃ r : Program,
      runs (featureResidualMapProgram f) x r ∧
      runs f r x ∧
      CompressionCondition f r x := by
  obtain ⟨p, hpRun⟩ := featureResidualPairSearcher_runs_of_feature hfeature
  obtain ⟨r, hpEq, hf, hcomp⟩ := featureResidualPairSearcher_sound hpRun
  refine ⟨r, ?_, hf, hcomp⟩
  rw [featureResidualMapProgram, runs_codeToProgram_iff]
  calc
    Code.eval (Classical.choose (exists_featureResidualMapCode f)) (BitString.toNatExact x) =
        (Code.eval (programToCode featureResidualPairSearcher)
          (Nat.pair (BitString.toNatExact f) (BitString.toNatExact x))).map
            (fun pairNat : Nat => pairNat.unpair.1) :=
          eval_featureResidualMapCode f (BitString.toNatExact x)
    _ = (Part.some (BitString.toNatExact p)).map (fun pairNat : Nat => pairNat.unpair.1) := by
          rw [show Code.eval (programToCode featureResidualPairSearcher)
              (Nat.pair (BitString.toNatExact f) (BitString.toNatExact x)) =
            Part.some (BitString.toNatExact p) by
              simpa [runs, toNatExact_packedInput] using hpRun]
    _ = Part.some (BitString.toNatExact r) := by
          simp [hpEq, toNatExact_packedInput]

/-- Uniform plain-program bound for residual maps built from features of length at most `n`. -/
noncomputable def shortFeatureResidualMapBound (n : Nat) : Nat :=
  ((BitString.allUpToLength n).toFinset).sup
    (fun f : Program => (BitString.blen (featureResidualMapProgram f) : Nat))

/-- Corresponding uniform prefix bound for the residual output from `x`. -/
noncomputable def shortFeatureResidualPrefixBound (n : Nat) : Nat :=
  shortFeatureResidualMapBound n +
    2 * BitString.blen (BitString.ofNat (shortFeatureResidualMapBound n)) +
    outerApplyInterpreterPrefixOverhead

private theorem featureResidualMapProgram_length_le_bound {f : Program} {n : Nat}
    (hf : BitString.blen f ≤ n) :
    BitString.blen (featureResidualMapProgram f) ≤ shortFeatureResidualMapBound n := by
  have hmem : f ∈ (BitString.allUpToLength n).toFinset := by
    exact List.mem_toFinset.mpr ((BitString.mem_allUpToLength_iff).2 hf)
  exact Finset.le_sup
    (s := (BitString.allUpToLength n).toFinset)
    (f := fun f : Program => (BitString.blen (featureResidualMapProgram f) : Nat))
    hmem

/-- The first half of Theorem 3.8: a feature whose length is bounded by `n` has some residual
recoverable from `x` with a prefix description bounded by a constant depending only on `n`. -/
theorem exists_shortResidual_of_feature_length_le
    {f x : Program} {n : Nat}
    (hfeature : IsFeature runs f x)
    (hf : BitString.blen f ≤ n) :
    ∃ q : Program,
      runs f q x ∧
      CompressionCondition f q x ∧
      PrefixConditionalComplexity q x ≤ shortFeatureResidualPrefixBound n := by
  obtain ⟨q, hg, hq, hcomp⟩ := featureResidualMapProgram_runs_of_feature hfeature
  refine ⟨q, hq, hcomp, ?_⟩
  have hplain : PrefixConditionalComplexity q x ≤
      BitString.blen (featureResidualMapProgram f) +
        2 * BitString.blen (BitString.ofNat (BitString.blen (featureResidualMapProgram f))) +
        outerApplyInterpreterPrefixOverhead := by
    exact prefixConditionalComplexity_le_plainProgramLength hg
  have hlen : BitString.blen (featureResidualMapProgram f) ≤ shortFeatureResidualMapBound n :=
    featureResidualMapProgram_length_le_bound hf
  have hmono :
      BitString.blen (BitString.ofNat (BitString.blen (featureResidualMapProgram f))) ≤
        BitString.blen (BitString.ofNat (shortFeatureResidualMapBound n)) := by
    exact BitString.blen_ofNat_mono hlen
  unfold shortFeatureResidualPrefixBound at *
  omega

/-- Any shortest descriptive map for a feature of length at most `n` is itself bounded by a
constant depending only on `n`. -/
theorem shortestDescriptiveMap_length_le_of_feature_length_le
    {f g x : Program} {n : Nat}
    (hshort : IsShortestDescriptiveMap runs f g x)
    (hf : BitString.blen f ≤ n) :
    BitString.blen g ≤ shortFeatureResidualMapBound n := by
  have hfeature : IsFeature runs f x := ⟨g, hshort.1⟩
  obtain ⟨r, hg, hr, hcomp⟩ := featureResidualMapProgram_runs_of_feature hfeature
  have hdesc : IsDescriptiveMap runs f (featureResidualMapProgram f) x := ⟨r, hg, hr, hcomp⟩
  exact le_trans (hshort.2 _ hdesc) (featureResidualMapProgram_length_le_bound hf)

/-- The residual output by a shortest descriptive map for a feature of length at most `n` also
has bounded conditional prefix complexity. -/
theorem shortestDescriptiveMap_output_prefix_le_of_feature_length_le
    {f g x r : Program} {n : Nat}
    (hshort : IsShortestDescriptiveMap runs f g x)
    (hr : runs g x r)
    (hf : BitString.blen f ≤ n) :
    PrefixConditionalComplexity r x ≤ shortFeatureResidualPrefixBound n := by
  have hgLen : BitString.blen g ≤ shortFeatureResidualMapBound n :=
    shortestDescriptiveMap_length_le_of_feature_length_le hshort hf
  have hplain : PrefixConditionalComplexity r x ≤
      BitString.blen g +
        2 * BitString.blen (BitString.ofNat (BitString.blen g)) +
        outerApplyInterpreterPrefixOverhead := by
    exact prefixConditionalComplexity_le_plainProgramLength hr
  have hmono :
      BitString.blen (BitString.ofNat (BitString.blen g)) ≤
        BitString.blen (BitString.ofNat (shortFeatureResidualMapBound n)) := by
    exact BitString.blen_ofNat_mono hgLen
  unfold shortFeatureResidualPrefixBound at *
  omega

/-- Theorem 3.8 in bounded form: once the feature length is bounded by `n`, both the canonical
residual and the residual of any shortest descriptive map are recoverable from `x` with a constant
bound depending only on `n`, and the shortest descriptive map itself has constant length. -/
theorem theorem38_of_feature_length_le
    {f g x : Program} {n : Nat}
    (hfeature : IsFeature runs f x)
    (hf : BitString.blen f ≤ n)
    (hshort : IsShortestDescriptiveMap runs f g x) :
    (∃ q : Program,
      runs f q x ∧
      CompressionCondition f q x ∧
      PrefixConditionalComplexity q x ≤ shortFeatureResidualPrefixBound n) ∧
    ∃ r : Program,
      runs g x r ∧
      runs f r x ∧
      CompressionCondition f r x ∧
      BitString.blen g = ConditionalComplexity r x ∧
      PrefixConditionalComplexity r x ≤ shortFeatureResidualPrefixBound n ∧
      BitString.blen g ≤ shortFeatureResidualMapBound n := by
  refine ⟨exists_shortResidual_of_feature_length_le hfeature hf, ?_⟩
  rcases hshort.1 with ⟨r, hr, hfRun, hcomp⟩
  refine ⟨r, hr, hfRun, hcomp, ?_, ?_, ?_⟩
  · exact shortestDescriptiveMap_eq_conditionalComplexity hshort hr hfRun hcomp
  · exact shortestDescriptiveMap_output_prefix_le_of_feature_length_le hshort hr hf
  · exact shortestDescriptiveMap_length_le_of_feature_length_le hshort hf

/-- Section 3.4 specialization of Theorem 3.8: for a shortest `b`-feature of a `b`-compressible
string, the bounds become constants depending only on `b` and the universal feature. -/
theorem theorem38_of_shortestBFeature
    {b : Nat} {f g x : Program}
    (hb : 1 < b)
    (hbc : BCompressible b x)
    (hshortF : IsShortestBFeature runs b f x)
    (hshortG : IsShortestDescriptiveMap runs f g x) :
    (∃ q : Program,
      runs f q x ∧
      CompressionCondition f q x ∧
      PrefixConditionalComplexity q x ≤
        shortFeatureResidualPrefixBound (bCompressibleFeatureBound b)) ∧
    ∃ r : Program,
      runs g x r ∧
      runs f r x ∧
      CompressionCondition f r x ∧
      BitString.blen g = ConditionalComplexity r x ∧
      PrefixConditionalComplexity r x ≤
        shortFeatureResidualPrefixBound (bCompressibleFeatureBound b) ∧
      BitString.blen g ≤ shortFeatureResidualMapBound (bCompressibleFeatureBound b) := by
  exact theorem38_of_feature_length_le
    (hfeature := bFeature_forgets hshortF.1)
    (hf := theorem37_shortestBFeature hb hbc hshortF)
    (hshort := hshortG)

end

end Compression

end IcTheory
