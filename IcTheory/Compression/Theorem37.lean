import IcTheory.Compression.Definition31
import IcTheory.Compression.Section2
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- A string is `b`-compressible if its plain complexity is at most a `1 / b` fraction of its
length. This is the paper's Section 3.4 notion of "compressible by a factor `b`". -/
def BCompressible (b : Nat) (x : Program) : Prop :=
  Complexity x ≤ BitString.blen x / b

/-- The constant bound from Theorem 3.7. -/
def bCompressibleFeatureBound (b : Nat) : Nat :=
  max universalFeatureConstant (universalFeatureConstant / (b - 1))

private theorem length_pos_of_feature {f x : Program}
    (hfeature : IsFeature runs f x) :
    0 < BitString.blen x := by
  exact lt_of_le_of_lt (Nat.zero_le _) (feature_length_lt hfeature)

private theorem length_pos_of_bFeature {b : Nat} {f x : Program}
    (hfeature : IsBFeature runs b f x) :
    0 < BitString.blen x := by
  exact length_pos_of_feature (bFeature_forgets hfeature)

private theorem compressible_of_bCompressible_of_shortestFeature
    {b : Nat} {f x : Program}
    (hb : 1 < b)
    (hshort : IsShortestFeature runs f x)
    (hbc : BCompressible b x) :
    Compressible x := by
  have hxpos : 0 < BitString.blen x :=
    length_pos_of_feature (shortestFeature_isFeature hshort)
  exact lt_of_le_of_lt hbc (Nat.div_lt_self hxpos hb)

private theorem compressible_of_bCompressible_of_shortestBFeature
    {b : Nat} {f x : Program}
    (hb : 1 < b)
    (hshort : IsShortestBFeature runs b f x)
    (hbc : BCompressible b x) :
    Compressible x := by
  have hxpos : 0 < BitString.blen x :=
    length_pos_of_bFeature hshort.1
  exact lt_of_le_of_lt hbc (Nat.div_lt_self hxpos hb)

/-- In the highly compressible branch, the universal feature is also a `b`-feature whenever the
shortest residual already satisfies the `1 / b` length bound. -/
theorem universalFeature_isBFeature_of_compressibleByMoreThan
    {b : Nat} {x : Program}
    (hcompress : CompressibleByMoreThan universalFeatureConstant x)
    (hbc : BCompressible b x) :
    IsBFeature runs b universalFeature x := by
  obtain ⟨r, hrLen, hrRuns⟩ := exists_program_forComplexity x
  refine ⟨UniversalMachine.codeToProgram (Nat.Partrec.Code.const (BitString.toNatExact r)), ?_⟩
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · exact (UniversalMachine.runs_const_iff (BitString.toNatExact r) x r).2
      (BitString.ofNatExact_toNatExact r).symm
  · exact (UniversalMachine.runs_universalFeature_iff r x).2 hrRuns
  · simpa [CompressionCondition, CompressibleByMoreThan,
      UniversalMachine.universalFeatureConstant, hrLen, Nat.add_comm] using hcompress
  · simpa [ResidualBoundByFactor, hrLen] using hbc

/-- In the highly compressible branch, shortest `b`-features are bounded by the universal-feature
constant. -/
theorem shortestBFeature_le_universalFeatureConstant
    {b : Nat} {f x : Program}
    (hshort : IsShortestBFeature runs b f x)
    (hcompress : CompressibleByMoreThan universalFeatureConstant x)
    (hbc : BCompressible b x) :
    BitString.blen f ≤ universalFeatureConstant := by
  exact hshort.2 universalFeature
    (universalFeature_isBFeature_of_compressibleByMoreThan hcompress hbc)

private theorem complexity_le_div_pred_of_not_compressibleByMoreThan
    {b : Nat} {x : Program}
    (hb : 1 < b)
    (hbc : BCompressible b x)
    (hnot : ¬ CompressibleByMoreThan universalFeatureConstant x) :
    Complexity x ≤ universalFeatureConstant / (b - 1) := by
  have hbpos : 0 < b := Nat.zero_lt_of_lt hb
  have hpredPos : 0 < b - 1 := Nat.sub_pos_of_lt hb
  have hmul : Complexity x * b ≤ BitString.blen x := by
    exact (Nat.le_div_iff_mul_le hbpos).1 hbc
  have hnot' : BitString.blen x ≤ Complexity x + universalFeatureConstant := by
    unfold CompressibleByMoreThan at hnot
    exact Nat.le_of_not_lt hnot
  have hmul' : Complexity x * b ≤ Complexity x + universalFeatureConstant := by
    exact le_trans hmul hnot'
  have hstep :
      Complexity x * (b - 1) + Complexity x ≤ universalFeatureConstant + Complexity x := by
    calc
      Complexity x * (b - 1) + Complexity x =
          Complexity x * ((b - 1) + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = Complexity x * b := by
            rw [show (b - 1) + 1 = b by omega]
      _ ≤ Complexity x + universalFeatureConstant := hmul'
      _ = universalFeatureConstant + Complexity x := by ac_rfl
  have hstep' :
      Complexity x + Complexity x * (b - 1) ≤ Complexity x + universalFeatureConstant := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
  have hcancel : Complexity x * (b - 1) ≤ universalFeatureConstant := by
    exact (Nat.add_le_add_iff_left).1 hstep'
  exact (Nat.le_div_iff_mul_le hpredPos).2 <|
    by simpa [Nat.mul_comm] using hcancel

/-- Theorem 3.7 for ordinary shortest features: for a `b`-compressible string, the length of a
shortest feature is bounded by a constant depending only on `b` and the universal feature. -/
theorem theorem37_shortestFeature
    {b : Nat} {f x : Program}
    (hb : 1 < b)
    (hbc : BCompressible b x)
    (hshort : IsShortestFeature runs f x) :
    BitString.blen f ≤ bCompressibleFeatureBound b := by
  by_cases hcompress : CompressibleByMoreThan universalFeatureConstant x
  · exact le_trans
      (shortestFeature_le_universalFeatureConstant hshort hcompress)
      (le_max_left _ _)
  · have hxcompress : Compressible x :=
      compressible_of_bCompressible_of_shortestFeature hb hshort hbc
    have hlen : BitString.blen f ≤ Complexity x :=
      shortestFeature_le_complexity hshort hxcompress
    have hk :
        Complexity x ≤ universalFeatureConstant / (b - 1) :=
      complexity_le_div_pred_of_not_compressibleByMoreThan hb hbc hcompress
    exact le_trans hlen (le_trans hk (le_max_right _ _))

/-- Theorem 3.7 for shortest `b`-features. -/
theorem theorem37_shortestBFeature
    {b : Nat} {f x : Program}
    (hb : 1 < b)
    (hbc : BCompressible b x)
    (hshort : IsShortestBFeature runs b f x) :
    BitString.blen f ≤ bCompressibleFeatureBound b := by
  by_cases hcompress : CompressibleByMoreThan universalFeatureConstant x
  · exact le_trans
      (shortestBFeature_le_universalFeatureConstant hshort hcompress hbc)
      (le_max_left _ _)
  · have hxcompress : Compressible x :=
      compressible_of_bCompressible_of_shortestBFeature hb hshort hbc
    have hlen : BitString.blen f ≤ Complexity x :=
      shortestBFeature_le_complexity hshort hxcompress
    have hk :
        Complexity x ≤ universalFeatureConstant / (b - 1) :=
      complexity_le_div_pred_of_not_compressibleByMoreThan hb hbc hcompress
    exact le_trans hlen (le_trans hk (le_max_right _ _))

end

end Compression

end IcTheory
