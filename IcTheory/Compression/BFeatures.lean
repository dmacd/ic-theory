import IcTheory.Compression.Definition31
import IcTheory.Compression.Theorem35
import IcTheory.Compression.Theorem34
import IcTheory.Compression.Theorem32
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

/-- The prefix-gap high-information reduction also applies to `b`-features, since they are
ordinary features after forgetting the extra residual bound. -/
theorem highInformationIn_of_bFeature_of_prefixGap {b : Nat} {f x : Program}
    (hfeature : IsBFeature runs b f x)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    HighInformationIn f x := by
  exact highInformationIn_of_feature_of_prefixGap (bFeature_forgets hfeature) hgap

/-- Prefix-gap version of Theorem 3.2 for shortest `b`-features. -/
theorem shortestBFeature_conditionalPrefixLogLe_of_prefixGap {b : Nat} {f x : Program}
    (hshort : IsShortestBFeature runs b f x)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  exact lemma33
    (shortestBFeature_forgets hshort)
    (highInformationIn_of_bFeature_of_prefixGap hshort.1 hgap)

/-- Equation (27) for shortest `b`-descriptive maps. The proof is identical to the ordinary
case once the `b`-specific conditional-complexity characterization is available. -/
theorem theorem34_eq27_of_shortestBDescriptiveMap_and_noSuperfluousPair_and_conditionalBridge
    {b : Nat} {f g x r : Program}
    (hshort : IsShortestBDescriptiveMap runs b f g x)
    (hr : runs g x r)
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x)
    (hres : ResidualBoundByFactor b r x)
    (hpair : NoSuperfluousPair r f x)
    (hbridge :
      LogLe (ConditionalComplexity r x) (PrefixConditionalComplexity r x) (BitString.blen x)) :
    LogLe (BitString.blen g) 0 (BitString.blen x) := by
  have hlen : BitString.blen g = ConditionalComplexity r x :=
    shortestBDescriptiveMap_eq_conditionalComplexity hshort hr hf hcomp hres
  rw [hlen]
  exact logLe_trans hbridge (noSuperfluousPair_residual hpair)

private theorem prefixComplexity_logLe_lengthBound {n : Nat} {p : Program}
    (hp : BitString.blen p ≤ n) :
    LogLe (PrefixComplexity p) (BitString.blen p) n := by
  exact prefixComplexity_log_upper_of_le hp

private theorem prefixConditionalComplexity_logLe_lengthBound {input p : Program} {n : Nat}
    (hp : BitString.blen p ≤ n) :
    LogLe (PrefixConditionalComplexity p input) (BitString.blen p) n := by
  have hcond :
      LogLe (PrefixConditionalComplexity p input) (PrefixComplexity p) n := by
    exact logLe_of_scale_le (prefixConditionalComplexity_logLe_prefixComplexity p input) hp
  exact logLe_trans hcond (prefixComplexity_logLe_lengthBound hp)

private theorem logLe_of_twiceScale {a b n : Nat}
    (hab : LogLe a b (n + n)) :
    LogLe a b n := by
  rcases hab with ⟨c, d, h⟩
  have hlog : logPenalty (n + n) ≤ 2 * logPenalty n + 1 := by
    have htmp := logPenalty_add_le n n
    omega
  have hmul : c * logPenalty (n + n) ≤ c * (2 * logPenalty n + 1) := by
    exact Nat.mul_le_mul_left c hlog
  refine ⟨2 * c, c + d, ?_⟩
  calc
    a ≤ b + c * logPenalty (n + n) + d := h
    _ ≤ b + c * (2 * logPenalty n + 1) + d := by
      omega
    _ = b + (2 * c) * logPenalty n + (c + d) := by
      ring_nf

private theorem upperScaleLogLe_of_lengthBounds {y z : Program} {n : Nat}
    (hy : BitString.blen y ≤ n)
    (hz : BitString.blen z ≤ n) :
    LogLe (PrefixComplexity y + PrefixConditionalComplexity z y) (n + n) (n + n) := by
  have hsum :
      LogLe (PrefixComplexity y + PrefixConditionalComplexity z y)
        (BitString.blen y + BitString.blen z)
        n := by
    exact logLe_add
      (prefixComplexity_logLe_lengthBound hy)
      (prefixConditionalComplexity_logLe_lengthBound (input := y) hz)
  have hbound :
      LogLe (BitString.blen y + BitString.blen z) (n + n) n := by
    exact logLe_of_le (Nat.add_le_add hy hz)
  exact logLe_of_scale_le (logLe_trans hsum hbound) (Nat.le_add_right n n)

private theorem jointComplexity_logLe_of_lengthBounds {y z : Program} {n : Nat}
    (hy : BitString.blen y ≤ n)
    (hz : BitString.blen z ≤ n) :
    LogLe (JointComplexity y z) (n + n) (n + n) := by
  have hscale := upperScaleLogLe_of_lengthBounds hy hz
  have hupper :
      JointUpperChainRuleAt (n + n) y z := by
    exact jointUpperChainRuleAt_of_interpreter_of_scale_logLe
      (u := jointUpperInterpreter) (x := y) (y := z)
      jointUpperInterpreter_isJointUpperInterpreter hscale
  exact logLe_trans hupper hscale

private theorem symmetricInformationBound_of_lengthBounds {y z : Program} {n : Nat}
    (hy : BitString.blen y ≤ n)
    (hz : BitString.blen z ≤ n) :
    LogLe (PrefixComplexity z + PrefixConditionalComplexity y z)
      (PrefixComplexity y + PrefixConditionalComplexity z y)
      n := by
  have hlower :
      JointLowerChainRuleAt (n + n) z y := by
    exact jointLowerChainRuleAt_concrete_of_scale_logLe
      (jointComplexity_logLe_of_lengthBounds hz hy)
  have hswap :
      JointSwapInvariantAt (n + n) z y := by
    exact jointSwapInvariantAt_of_logBounds
      (jointComplexity_logLe_of_lengthBounds hz hy)
      (jointComplexity_logLe_of_lengthBounds hy hz)
  have hupper :
      JointUpperChainRuleAt (n + n) y z := by
    exact jointUpperChainRuleAt_of_interpreter_of_scale_logLe
      (u := jointUpperInterpreter) (x := y) (y := z)
      jointUpperInterpreter_isJointUpperInterpreter
      (upperScaleLogLe_of_lengthBounds hy hz)
  exact logLe_of_twiceScale (symmetricInformationBound_of_jointRulesAt hlower hswap hupper)

private theorem prefixInformation_logLe_swap_of_lengthBounds {y z : Program} {n : Nat}
    (hy : BitString.blen y ≤ n)
    (hz : BitString.blen z ≤ n) :
    LogLe (PrefixInformation y z) (PrefixInformation z y) n := by
  rcases symmetricInformationBound_of_lengthBounds hy hz with ⟨c, d, h⟩
  refine ⟨c, d, ?_⟩
  have hySplit :
      PrefixComplexity y ≤ PrefixInformation z y + PrefixConditionalComplexity y z := by
    unfold PrefixInformation
    omega
  have hzBound :
      PrefixComplexity z ≤
        PrefixInformation z y + PrefixConditionalComplexity z y +
          c * logPenalty n + d := by
    have h' :
        PrefixComplexity z + PrefixConditionalComplexity y z ≤
          PrefixInformation z y + PrefixConditionalComplexity y z +
            PrefixConditionalComplexity z y + c * logPenalty n + d := by
      omega
    have h'' :
        PrefixConditionalComplexity y z + PrefixComplexity z ≤
          PrefixConditionalComplexity y z +
            (PrefixInformation z y + PrefixConditionalComplexity z y +
              c * logPenalty n + d) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h'
    exact Nat.le_of_add_le_add_left h''
  exact (Nat.sub_le_iff_le_add').2 <| by
    simpa [PrefixInformation, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hzBound

private theorem prefixInformation_symm_of_lengthBounds {y z : Program} {n : Nat}
    (hy : BitString.blen y ≤ n)
    (hz : BitString.blen z ≤ n) :
    LogEq (PrefixInformation y z) (PrefixInformation z y) n := by
  exact ⟨prefixInformation_logLe_swap_of_lengthBounds hy hz,
    prefixInformation_logLe_swap_of_lengthBounds hz hy⟩

private theorem prefixConditionalComplexity_self_logLe_zero (x : Program) :
    LogLe (PrefixConditionalComplexity x x) 0 (BitString.blen x) := by
  let p : Program := codeToProgram Code.id
  have hx :
      PrefixConditionalComplexity x x ≤
        BitString.blen p + 2 * BitString.blen (BitString.ofNat (BitString.blen p)) +
          outerApplyInterpreterPrefixOverhead := by
    exact prefixConditionalComplexity_le_plainProgramLength
      ((runs_id_iff x x).2 rfl)
  refine ⟨0,
    BitString.blen p + 2 * BitString.blen (BitString.ofNat (BitString.blen p)) +
      outerApplyInterpreterPrefixOverhead, ?_⟩
  simpa [p] using hx

/-- One `b`-compression step in the current prefix-facing theory. This is the exact analogue of
`IsPrefixCompressionStep`, with shortestness measured among `b`-features. -/
def IsBPrefixCompressionStep (b : Nat) (x f r : Program) : Prop :=
  IsShortestBFeature runs b f x ∧
    runs f r x ∧
    CompressionCondition f r x ∧
    BitString.blen f ≤ PrefixConditionalComplexity x r ∧
    NoSuperfluousPair r f x

private theorem feature_length_le_of_bPrefixCompressionStep {b : Nat} {x f r : Program}
    (hstep : IsBPrefixCompressionStep b x f r) :
    BitString.blen f ≤ BitString.blen x := by
  rcases hstep with ⟨hshort, _, _, _, _⟩
  exact (feature_length_lt (shortestBFeature_forgets hshort)).le

private theorem residual_length_lt_of_bPrefixCompressionStep {b : Nat} {x f r : Program}
    (hstep : IsBPrefixCompressionStep b x f r) :
    BitString.blen r < BitString.blen x := by
  rcases hstep with ⟨_, _, hcomp, _, _⟩
  unfold CompressionCondition at hcomp
  omega

/-- `b`-version of the inductive incremental compression chain. -/
inductive IsIncrementalBPrefixCompression (b : Nat) : Program → List Program → Program → Prop
  | nil (x : Program) :
      IsIncrementalBPrefixCompression b x [] x
  | cons {x f r rs : Program} {fs : List Program}
      (hstep : IsBPrefixCompressionStep b x f r)
      (hrest : IsIncrementalBPrefixCompression b r fs rs) :
      IsIncrementalBPrefixCompression b x (f :: fs) rs

private theorem residual_length_le_of_bIncrementalCompression
    {b : Nat} {x rs : Program} {fs : List Program}
    (hchain : IsIncrementalBPrefixCompression b x fs rs) :
    BitString.blen rs ≤ BitString.blen x := by
  induction hchain with
  | nil x =>
      simp
  | @cons x f r rs fs hstep hrest ih =>
      exact le_trans ih (residual_length_lt_of_bPrefixCompressionStep hstep).le

private theorem split_incrementalBPrefixCompression {b : Nat} {x rs : Program}
    {gs hs : List Program}
    (hchain : IsIncrementalBPrefixCompression b x (gs ++ hs) rs) :
    ∃ rmid : Program,
      IsIncrementalBPrefixCompression b x gs rmid ∧
        IsIncrementalBPrefixCompression b rmid hs rs := by
  induction gs generalizing x rs with
  | nil =>
      refine ⟨x, IsIncrementalBPrefixCompression.nil (b := b) x, ?_⟩
      simpa using hchain
  | cons g gs ih =>
      cases hchain with
      | cons hstep hrest =>
          obtain ⟨rmid, hleft, hright⟩ := ih hrest
          exact ⟨rmid, IsIncrementalBPrefixCompression.cons hstep hleft, hright⟩

private theorem targetFeature_length_le_of_bChain
    {b : Nat} {x rs f : Program} {gs hs : List Program}
    (hchain : IsIncrementalBPrefixCompression b x (gs ++ f :: hs) rs) :
    BitString.blen f ≤ BitString.blen x := by
  induction gs generalizing x rs with
  | nil =>
      cases hchain with
      | cons hstep _ =>
          simpa using feature_length_le_of_bPrefixCompressionStep hstep
  | cons g gs ih =>
      cases hchain with
      | cons hstep hrest =>
          exact le_trans (ih hrest) (residual_length_lt_of_bPrefixCompressionStep hstep).le

private theorem feature_after_bPrefixConditional_stepLog
    {b : Nat} {x rs f : Program} {gs hs : List Program}
    (hchain : IsIncrementalBPrefixCompression b x (gs ++ f :: hs) rs) :
    StepLogLe (PrefixConditionalComplexity f x) 0 (2 * gs.length + 1) (BitString.blen x) := by
  induction gs generalizing x rs with
  | nil =>
      cases hchain with
      | cons hstep _ =>
          rcases hstep with ⟨_, _, _, _, hpair⟩
          simpa using stepLogLe_of_logLe (noSuperfluousPair_feature hpair)
  | cons g gs ih =>
      cases hchain with
      | @cons x _ r rs _ hstep0 hrest =>
          rcases hstep0 with ⟨hshort0, hf0, hcomp0, hprefix0, hpair⟩
          have hir :
              StepLogLe (PrefixConditionalComplexity f r) 0 (2 * gs.length + 1) (BitString.blen r) :=
            ih hrest
          have hir' :
              StepLogLe (PrefixConditionalComplexity f r) 0 (2 * gs.length + 1) (BitString.blen x) := by
            exact stepLogLe_of_scale_le hir
              (residual_length_lt_of_bPrefixCompressionStep
                ⟨hshort0, hf0, hcomp0, hprefix0, hpair⟩).le
          have hrx :
              StepLogLe (PrefixConditionalComplexity r x) 0 1 (BitString.blen x) := by
            simpa using stepLogLe_of_logLe (noSuperfluousPair_residual hpair)
          have hsum :
              StepLogLe
                (PrefixConditionalComplexity r x + PrefixConditionalComplexity f r)
                0
                (1 + (2 * gs.length + 1))
                (BitString.blen x) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using stepLogLe_add hrx hir'
          have hsumScale :
              LogLe
                (PrefixConditionalComplexity r x + PrefixConditionalComplexity f r)
                (BitString.blen x)
                (BitString.blen x) := by
            exact logLe_trans (logLe_of_stepLogLe hsum) (logLe_of_le (Nat.zero_le _))
          have hcomp :
              LogLe (PrefixConditionalComplexity f x)
                (PrefixConditionalComplexity r x + PrefixConditionalComplexity f r)
                (BitString.blen x) := by
            exact logLe_of_scale_logLe
              (prefixConditionalComplexity_logLe_of_conditionalCompose
                (u := conditionalComposeInterpreter)
                (input := x) (z := r) (y := f)
                conditionalComposeInterpreter_isConditionalComposeInterpreter)
              hsumScale
          have hstep :
              StepLogLe (PrefixConditionalComplexity f x)
                (PrefixConditionalComplexity r x + PrefixConditionalComplexity f r)
                1
                (BitString.blen x) := by
            exact stepLogLe_of_logLe hcomp
          have hfinal := stepLogLe_trans hstep hsum
          have hs : 1 + (1 + (1 + 2 * gs.length)) = 1 + (2 + 2 * gs.length) := by
            omega
          simpa [hs, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

private theorem prefixInformation_small_of_bPrefixCompressionStep {b : Nat} {x f r : Program}
    (hstep : IsBPrefixCompressionStep b x f r) :
    LogLe (PrefixInformation f r) 0 (BitString.blen x) := by
  rcases hstep with ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩
  have hrf :
      LogLe (PrefixInformation r f) 0 (BitString.blen x) := by
    exact logLe_of_scale_le
      (by
        simpa [featureGap] using
          (theorem33_eq16_of_prefixShortestBridge
            (fStar := f) (f := f) (x := x) (r := r) hshortPrefix hf))
      (feature_length_le_of_bPrefixCompressionStep ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩)
  have hsymm :
      LogEq (PrefixInformation f r) (PrefixInformation r f) (BitString.blen x) := by
    exact prefixInformation_symm_of_lengthBounds
      (feature_length_le_of_bPrefixCompressionStep ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩)
      (residual_length_lt_of_bPrefixCompressionStep ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩).le
  exact logLe_trans hsymm.1 hrf

/-- One `b`-compression step already gives the one-step form of the Theorem 3.6 decomposition. -/
theorem stepLogEq_of_bPrefixCompressionStep {b : Nat} {x f r : Program}
    (hstep : IsBPrefixCompressionStep b x f r) :
    StepLogEq (PrefixComplexity x)
      (PrefixComplexity f + PrefixComplexity r)
      1
      (BitString.blen x) := by
  rcases hstep with ⟨_hshort, hf, hcomp, hshortPrefix, hpair⟩
  exact stepLogEq_of_logEq <|
    theorem34_eq28_of_prefixShortestBridge_and_noSuperfluousPair hshortPrefix hf hcomp hpair

/-- Prefix-form Theorem 3.6 for `b`-features. -/
theorem theorem36_prefix_b {b : Nat} {x rs : Program} {fs : List Program}
    (hchain : IsIncrementalBPrefixCompression b x fs rs) :
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
        stepLogEq_of_bPrefixCompressionStep hstep
      have hrestEq :
          StepLogEq (PrefixComplexity r)
            (featurePrefixComplexitySum fs + PrefixComplexity rs)
            fs.length
            (BitString.blen x) := by
        exact stepLogEq_of_scale_le ih (residual_length_lt_of_bPrefixCompressionStep hstep).le
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

/-- Forward half of Theorem 3.5 for incremental compression by shortest `b`-features. -/
theorem theorem35_b_forward
    {b : Nat} {x rs fi fj : Program} {pre mid post : List Program}
    (hchain : IsIncrementalBPrefixCompression b x (pre ++ [fi] ++ mid ++ [fj] ++ post) rs) :
    StepLogLe (PrefixInformation fi fj) 0 (2 * mid.length + 3) (BitString.blen x) := by
  obtain ⟨rpre, hpre, hsuffix⟩ := split_incrementalBPrefixCompression
    (gs := pre) (hs := [fi] ++ mid ++ [fj] ++ post) <| by
      simpa [List.append_assoc] using hchain
  cases hsuffix with
  | @cons _ _ r _ _ hstepFi hafter =>
      have hriLen : BitString.blen r ≤ BitString.blen x := by
        exact le_trans (residual_length_lt_of_bPrefixCompressionStep hstepFi).le
          (residual_length_le_of_bIncrementalCompression hpre)
      have hfjLen :
          BitString.blen fj ≤ BitString.blen x := by
        have hfjAtR :
            BitString.blen fj ≤ BitString.blen r := by
          exact targetFeature_length_le_of_bChain
            (x := r) (rs := rs) (f := fj) (gs := mid) (hs := post) <| by
              simpa [List.append_assoc] using hafter
        exact le_trans hfjAtR hriLen
      have hinfoFiRi :
          LogLe (PrefixInformation fi r) 0 (BitString.blen x) := by
        exact logLe_of_scale_le
          (prefixInformation_small_of_bPrefixCompressionStep hstepFi)
          (residual_length_le_of_bIncrementalCompression hpre)
      have hfjFromRi :
          StepLogLe (PrefixConditionalComplexity fj r) 0 (2 * mid.length + 1) (BitString.blen x) := by
        exact stepLogLe_of_scale_le
          (feature_after_bPrefixConditional_stepLog
            (b := b) (x := r) (rs := rs) (f := fj) (gs := mid) (hs := post) <| by
              simpa [List.append_assoc] using hafter)
          hriLen
      have hsum :
          StepLogLe (PrefixInformation fi r + PrefixConditionalComplexity fj r)
            0
            (1 + (2 * mid.length + 1))
            (BitString.blen x) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          stepLogLe_add (stepLogLe_of_logLe hinfoFiRi) hfjFromRi
      have hlemma0 :
          LogLe (PrefixInformation fi fj)
            (PrefixInformation fi r + PrefixConditionalComplexity fj r)
            (max (BitString.blen r) (BitString.blen fj)) := by
        exact lemma34 (x := fi) (y := r) (z := fj)
      have hlemma :
          LogLe (PrefixInformation fi fj)
            (PrefixInformation fi r + PrefixConditionalComplexity fj r)
            (BitString.blen x) := by
        exact logLe_of_scale_le hlemma0 (max_le hriLen hfjLen)
      have hfinal := stepLogLe_trans (stepLogLe_of_logLe hlemma) hsum
      have hs : 1 + (1 + (1 + 2 * mid.length)) = 2 * mid.length + 3 := by
        omega
      simpa [hs, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

/-- Reverse half of Theorem 3.5 for incremental compression by shortest `b`-features. -/
theorem theorem35_b_backward
    {b : Nat} {x rs fi fj : Program} {pre mid post : List Program}
    (hchain : IsIncrementalBPrefixCompression b x (pre ++ [fi] ++ mid ++ [fj] ++ post) rs) :
    StepLogLe (PrefixInformation fj fi) 0 (2 * mid.length + 4) (BitString.blen x) := by
  have hforward := theorem35_b_forward (b := b) (x := x) (rs := rs)
    (fi := fi) (fj := fj) (pre := pre) (mid := mid) (post := post) hchain
  have hfiLen :
      BitString.blen fi ≤ BitString.blen x := by
    exact targetFeature_length_le_of_bChain
      (b := b) (x := x) (rs := rs) (f := fi) (gs := pre) (hs := mid ++ [fj] ++ post) <| by
        simpa [List.append_assoc] using hchain
  have hfjLen :
      BitString.blen fj ≤ BitString.blen x := by
    exact targetFeature_length_le_of_bChain
      (b := b) (x := x) (rs := rs) (f := fj) (gs := pre ++ [fi] ++ mid) (hs := post) <| by
        simpa [List.append_assoc] using hchain
  have hsymm :
      LogEq (PrefixInformation fj fi) (PrefixInformation fi fj) (BitString.blen x) := by
    exact prefixInformation_symm_of_lengthBounds hfjLen hfiLen
  have hfinal := stepLogLe_trans (stepLogLe_of_logLe hsymm.1) hforward
  have hs : 1 + (2 * mid.length + 3) = 2 * mid.length + 4 := by
    omega
  simpa [hs, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

/-- Split-form Theorem 3.5 for incremental compression by shortest `b`-features. -/
theorem theorem35_b_split
    {b : Nat} {x rs fi fj : Program} {pre mid post : List Program}
    (hchain : IsIncrementalBPrefixCompression b x (pre ++ [fi] ++ mid ++ [fj] ++ post) rs) :
    StepLogLe (PrefixInformation fi fj) 0 (2 * mid.length + 4) (BitString.blen x) ∧
      StepLogLe (PrefixInformation fj fi) 0 (2 * mid.length + 4) (BitString.blen x) := by
  refine ⟨?_, theorem35_b_backward hchain⟩
  exact stepLogLe_of_stepCount_le (theorem35_b_forward hchain) (by omega)

private theorem incrementalBCompression_index_split
    {b : Nat} {x rs : Program} {fs : List Program} {i j : Nat}
    (hi : i < fs.length)
    (hj : j < fs.length)
    (hij : i < j)
    (hchain : IsIncrementalBPrefixCompression b x fs rs) :
    IsIncrementalBPrefixCompression b x
      (fs.take i ++ [fs[i]] ++ (fs.drop (i + 1)).take (j - i - 1) ++ [fs[j]] ++ fs.drop (j + 1))
      rs := by
  have hmid :
      (fs.drop (i + 1)).drop (j - i - 1) = fs[j] :: fs.drop (j + 1) := by
    have hk : j - i - 1 < (fs.drop (i + 1)).length := by
      rw [List.length_drop]
      omega
    have hji : i + (1 + (j - i - 1)) = j := by
      omega
    calc
      (fs.drop (i + 1)).drop (j - i - 1) =
          (fs.drop (i + 1))[j - i - 1] :: (fs.drop (i + 1)).drop ((j - i - 1) + 1) := by
        simpa using (List.cons_getElem_drop_succ (l := fs.drop (i + 1)) (n := j - i - 1) (h := hk)).symm
      _ = fs[j] :: fs.drop (j + 1) := by
        simp [List.getElem_drop, List.drop_drop, hji, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hsplit :
      fs =
        fs.take i ++ [fs[i]] ++ (fs.drop (i + 1)).take (j - i - 1) ++ [fs[j]] ++ fs.drop (j + 1) := by
    calc
      fs = fs.take i ++ fs.drop i := by
        simpa using (List.take_append_drop i fs).symm
      _ = fs.take i ++ (fs[i] :: fs.drop (i + 1)) := by
        rw [(List.cons_getElem_drop_succ (l := fs) (n := i) (h := hi)).symm]
      _ = fs.take i ++ [fs[i]] ++ fs.drop (i + 1) := by
        simp [List.append_assoc]
      _ = fs.take i ++ [fs[i]] ++
            ((fs.drop (i + 1)).take (j - i - 1) ++ (fs.drop (i + 1)).drop (j - i - 1)) := by
        simpa [List.append_assoc] using
          congrArg (fun t => fs.take i ++ [fs[i]] ++ t)
            (List.take_append_drop (j - i - 1) (fs.drop (i + 1))).symm
      _ = fs.take i ++ [fs[i]] ++ (fs.drop (i + 1)).take (j - i - 1) ++
            (fs.drop (i + 1)).drop (j - i - 1) := by
        simp [List.append_assoc]
      _ = fs.take i ++ [fs[i]] ++ (fs.drop (i + 1)).take (j - i - 1) ++ [fs[j]] ++ fs.drop (j + 1) := by
        rw [hmid]
        simp [List.append_assoc]
  have hrewritten : IsIncrementalBPrefixCompression b x
      (fs.take i ++ [fs[i]] ++ (fs.drop (i + 1)).take (j - i - 1) ++ [fs[j]] ++ fs.drop (j + 1))
      rs := by
    rw [← hsplit]
    exact hchain
  exact hrewritten

private theorem theorem35_b_of_ltIndices
    {b : Nat} {x rs : Program} {fs : List Program} {i j : Nat}
    (hchain : IsIncrementalBPrefixCompression b x fs rs)
    (hi : i < fs.length)
    (hj : j < fs.length)
    (hij : i < j) :
    StepLogLe (PrefixInformation fs[i] fs[j]) 0 (2 * (j - i - 1) + 4) (BitString.blen x) ∧
      StepLogLe (PrefixInformation fs[j] fs[i]) 0 (2 * (j - i - 1) + 4) (BitString.blen x) := by
  have hmidLen : ((fs.drop (i + 1)).take (j - i - 1)).length = j - i - 1 := by
    simp [List.length_take, List.length_drop]
    omega
  simpa [hmidLen] using
    theorem35_b_split
      (b := b) (x := x) (rs := rs) (fi := fs[i]) (fj := fs[j])
      (pre := fs.take i)
      (mid := (fs.drop (i + 1)).take (j - i - 1))
      (post := fs.drop (j + 1))
      (incrementalBCompression_index_split hi hj hij hchain)

/-- Prefix-form Theorem 3.5 for incremental compression by shortest `b`-features. -/
theorem theorem35_b
    {b : Nat} {x rs : Program} {fs : List Program} {i j : Nat}
    (hchain : IsIncrementalBPrefixCompression b x fs rs)
    (hi : i < fs.length)
    (hj : j < fs.length)
    (hij : i ≠ j) :
    StepLogLe (PrefixInformation fs[i] fs[j]) 0
      (2 * (Nat.dist i j - 1) + 4)
      (BitString.blen x) ∧
      StepLogLe (PrefixInformation fs[j] fs[i]) 0
      (2 * (Nat.dist i j - 1) + 4)
      (BitString.blen x) := by
  rcases Nat.lt_or_gt_of_ne hij with hij' | hij'
  · have hlt :=
      theorem35_b_of_ltIndices hchain hi hj hij'
    have hdist : Nat.dist i j = j - i := by
      exact Nat.dist_eq_sub_of_le hij'.le
    simpa [hdist] using hlt
  · have hlt :=
      theorem35_b_of_ltIndices hchain hj hi hij'
    have hdist : Nat.dist i j = i - j := by
      exact Nat.dist_eq_sub_of_le_right hij'.le
    have hswap :
        StepLogLe (PrefixInformation fs[i] fs[j]) 0 (2 * (i - j - 1) + 4) (BitString.blen x) ∧
          StepLogLe (PrefixInformation fs[j] fs[i]) 0 (2 * (i - j - 1) + 4) (BitString.blen x) := by
      exact ⟨hlt.2, hlt.1⟩
    simpa [hdist] using hswap

end

end Compression

end IcTheory
