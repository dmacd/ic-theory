import IcTheory.Compression.Theorem36
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

private theorem feature_length_le_of_prefixCompressionStep {x f r : Program}
    (hstep : IsPrefixCompressionStep x f r) :
    BitString.blen f ≤ BitString.blen x := by
  rcases hstep with ⟨hshort, _, _, _, _⟩
  exact (feature_length_lt (shortestFeature_isFeature hshort)).le

private theorem residual_length_lt_of_prefixCompressionStep {x f r : Program}
    (hstep : IsPrefixCompressionStep x f r) :
    BitString.blen r < BitString.blen x := by
  rcases hstep with ⟨_, _, hcomp, _, _⟩
  unfold CompressionCondition at hcomp
  omega

private theorem residual_length_le_of_incrementalCompression {x rs : Program} {fs : List Program}
    (hchain : IsIncrementalPrefixCompression x fs rs) :
    BitString.blen rs ≤ BitString.blen x := by
  induction hchain with
  | nil x =>
      simp
  | @cons x f r rs fs hstep hrest ih =>
      exact le_trans ih (residual_length_lt_of_prefixCompressionStep hstep).le

private theorem split_incrementalCompression {x rs : Program} {gs hs : List Program}
    (hchain : IsIncrementalPrefixCompression x (gs ++ hs) rs) :
    ∃ rmid : Program,
      IsIncrementalPrefixCompression x gs rmid ∧
        IsIncrementalPrefixCompression rmid hs rs := by
  induction gs generalizing x rs with
  | nil =>
      refine ⟨x, IsIncrementalPrefixCompression.nil x, ?_⟩
      simpa using hchain
  | cons g gs ih =>
      cases hchain with
      | cons hstep hrest =>
          obtain ⟨rmid, hleft, hright⟩ := ih hrest
          exact ⟨rmid, IsIncrementalPrefixCompression.cons hstep hleft, hright⟩

private theorem targetFeature_length_le_of_chain
    {x rs f : Program} {gs hs : List Program}
    (hchain : IsIncrementalPrefixCompression x (gs ++ f :: hs) rs) :
    BitString.blen f ≤ BitString.blen x := by
  induction gs generalizing x rs with
  | nil =>
      cases hchain with
      | cons hstep _ =>
          simpa using feature_length_le_of_prefixCompressionStep hstep
  | cons g gs ih =>
      cases hchain with
      | cons hstep hrest =>
          exact le_trans (ih hrest) (residual_length_lt_of_prefixCompressionStep hstep).le

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

private theorem prefixConditionalComplexity_compose_logLe_of_lengthBounds
    {x y z : Program} {n : Nat}
    (hy : BitString.blen y ≤ n)
    (hz : BitString.blen z ≤ n) :
    LogLe (PrefixConditionalComplexity y x)
      (PrefixConditionalComplexity z x + PrefixConditionalComplexity y z)
      n := by
  have hbase :
      LogLe (PrefixConditionalComplexity y x)
        (PrefixConditionalComplexity z x + PrefixConditionalComplexity y z)
        (PrefixConditionalComplexity z x + PrefixConditionalComplexity y z) := by
    exact prefixConditionalComplexity_logLe_of_conditionalCompose
      (u := conditionalComposeInterpreter)
      (input := x) (z := z) (y := y)
      conditionalComposeInterpreter_isConditionalComposeInterpreter
  have hscale :
      LogLe (PrefixConditionalComplexity z x + PrefixConditionalComplexity y z)
        (n + n)
        (n + n) := by
    have hsum :
        LogLe (PrefixConditionalComplexity z x + PrefixConditionalComplexity y z)
          (BitString.blen z + BitString.blen y)
          n := by
      exact logLe_add
        (prefixConditionalComplexity_logLe_lengthBound (input := x) hz)
        (prefixConditionalComplexity_logLe_lengthBound (input := z) hy)
    have hbound :
        LogLe (BitString.blen z + BitString.blen y) (n + n) n := by
      exact logLe_of_le (Nat.add_le_add hz hy)
    exact logLe_of_scale_le (logLe_trans hsum hbound) (Nat.le_add_right n n)
  exact logLe_of_twiceScale (logLe_of_scale_logLe hbase hscale)

/-- Prefix-form Lemma 3.4 at a bounded ambient scale. If `y` and `z` are both at most `n` bits
long, then the information in `x` about `z` is bounded by the information in `x` about `y` plus a
description of `z` from `y`, with logarithmic slack at scale `n`. -/
theorem lemma34_of_lengthBounds {x y z : Program} {n : Nat}
    (hy : BitString.blen y ≤ n)
    (hz : BitString.blen z ≤ n) :
    LogLe (PrefixInformation x z)
      (PrefixInformation x y + PrefixConditionalComplexity z y)
      n := by
  rcases symmetricInformationBound_of_lengthBounds hy hz with ⟨c₁, d₁, h₁⟩
  rcases prefixConditionalComplexity_compose_logLe_of_lengthBounds
      (x := x) (y := y) (z := z) hy hz with ⟨c₂, d₂, h₂⟩
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  have hySplit :
      PrefixComplexity y ≤ PrefixInformation x y + PrefixConditionalComplexity y x := by
    unfold PrefixInformation
    omega
  have hsum :
      PrefixComplexity z + PrefixConditionalComplexity y x ≤
        PrefixComplexity y + PrefixConditionalComplexity z y +
          PrefixConditionalComplexity z x +
          (c₁ + c₂) * logPenalty n + (d₁ + d₂) := by
    have hsum1 :
        PrefixComplexity z + PrefixConditionalComplexity y x ≤
          PrefixComplexity y + PrefixConditionalComplexity z y +
            PrefixConditionalComplexity z x +
            c₁ * logPenalty n + d₁ +
            (c₂ * logPenalty n + d₂) := by
      omega
    exact le_trans hsum1 <| by
      rw [Nat.add_mul]
      omega
  have hsum' :
      PrefixComplexity z + PrefixConditionalComplexity y x ≤
        PrefixInformation x y + PrefixConditionalComplexity y x +
          PrefixConditionalComplexity z y + PrefixConditionalComplexity z x +
          (c₁ + c₂) * logPenalty n + (d₁ + d₂) := by
    omega
  have hzBound :
      PrefixComplexity z ≤
        PrefixInformation x y + PrefixConditionalComplexity z y +
          PrefixConditionalComplexity z x +
          (c₁ + c₂) * logPenalty n + (d₁ + d₂) := by
    have hsum'' :
        PrefixConditionalComplexity y x + PrefixComplexity z ≤
          PrefixConditionalComplexity y x +
            (PrefixInformation x y + PrefixConditionalComplexity z y +
              PrefixConditionalComplexity z x +
              (c₁ + c₂) * logPenalty n + (d₁ + d₂)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum'
    exact Nat.le_of_add_le_add_left hsum''
  exact (Nat.sub_le_iff_le_add').2 <| by
    simpa [PrefixInformation, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hzBound

/-- Prefix-form Lemma 3.4 at its canonical ambient scale. -/
theorem lemma34 {x y z : Program} :
    LogLe (PrefixInformation x z)
      (PrefixInformation x y + PrefixConditionalComplexity z y)
      (max (BitString.blen y) (BitString.blen z)) := by
  exact lemma34_of_lengthBounds (Nat.le_max_left _ _) (Nat.le_max_right _ _)

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

private theorem feature_after_prefix_conditional_stepLog
    {x rs f : Program} {gs hs : List Program}
    (hchain : IsIncrementalPrefixCompression x (gs ++ f :: hs) rs) :
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
              (residual_length_lt_of_prefixCompressionStep
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

private theorem prefixInformation_small_of_prefixCompressionStep {x f r : Program}
    (hstep : IsPrefixCompressionStep x f r) :
    LogLe (PrefixInformation f r) 0 (BitString.blen x) := by
  rcases hstep with ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩
  have hrf :
      LogLe (PrefixInformation r f) 0 (BitString.blen x) := by
    exact logLe_of_scale_le
      (by
        simpa [featureGap] using
          (theorem33_eq16_of_prefixShortestBridge
            (fStar := f) (f := f) (x := x) (r := r) hshortPrefix hf))
      (feature_length_le_of_prefixCompressionStep ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩)
  have hsymm :
      LogEq (PrefixInformation f r) (PrefixInformation r f) (BitString.blen x) := by
    exact prefixInformation_symm_of_lengthBounds
      (feature_length_le_of_prefixCompressionStep ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩)
      (residual_length_lt_of_prefixCompressionStep ⟨hshort, hf, hcomp, hshortPrefix, hpair⟩).le
  exact logLe_trans hsymm.1 hrf

/-- Forward half of Theorem 3.5: if `fj` appears later than `fi` in an incremental compression
chain, then the information in `fi` about `fj` is bounded by the number of intervening steps. The
distance parameter here is `mid.length + 1`, encoded via `StepLogLe`. -/
theorem theorem35_forward
    {x rs fi fj : Program} {pre mid post : List Program}
    (hchain : IsIncrementalPrefixCompression x (pre ++ [fi] ++ mid ++ [fj] ++ post) rs) :
    StepLogLe (PrefixInformation fi fj) 0 (2 * mid.length + 3) (BitString.blen x) := by
  obtain ⟨rpre, hpre, hsuffix⟩ := split_incrementalCompression
    (gs := pre) (hs := [fi] ++ mid ++ [fj] ++ post) <| by
      simpa [List.append_assoc] using hchain
  cases hsuffix with
  | @cons _ _ r _ _ hstepFi hafter =>
      have hriLen : BitString.blen r ≤ BitString.blen x := by
        exact le_trans (residual_length_lt_of_prefixCompressionStep hstepFi).le
          (residual_length_le_of_incrementalCompression hpre)
      have hfjLen :
          BitString.blen fj ≤ BitString.blen x := by
        have hfjAtR :
            BitString.blen fj ≤ BitString.blen r := by
          exact targetFeature_length_le_of_chain
            (x := r) (rs := rs) (f := fj) (gs := mid) (hs := post) <| by
              simpa [List.append_assoc] using hafter
        exact le_trans hfjAtR hriLen
      have hinfoFiRi :
          LogLe (PrefixInformation fi r) 0 (BitString.blen x) := by
        exact logLe_of_scale_le
          (prefixInformation_small_of_prefixCompressionStep hstepFi)
          (residual_length_le_of_incrementalCompression hpre)
      have hfjFromRi :
          StepLogLe (PrefixConditionalComplexity fj r) 0 (2 * mid.length + 1) (BitString.blen x) := by
        exact stepLogLe_of_scale_le
          (feature_after_prefix_conditional_stepLog
            (x := r) (rs := rs) (f := fj) (gs := mid) (hs := post) <| by
              simpa [List.append_assoc] using hafter)
          hriLen
      have hsum :
          StepLogLe (PrefixInformation fi r + PrefixConditionalComplexity fj r)
            0
            (1 + (2 * mid.length + 1))
            (BitString.blen x) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          stepLogLe_add (stepLogLe_of_logLe hinfoFiRi) hfjFromRi
      have hlemma :
          LogLe (PrefixInformation fi fj)
            (PrefixInformation fi r + PrefixConditionalComplexity fj r)
            (BitString.blen x) := by
        exact lemma34_of_lengthBounds (x := fi) (y := r) (z := fj) hriLen hfjLen
      have hfinal := stepLogLe_trans (stepLogLe_of_logLe hlemma) hsum
      have hs : 1 + (1 + (1 + 2 * mid.length)) = 2 * mid.length + 3 := by
        omega
      simpa [hs, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

/-- Reverse half of Theorem 3.5, obtained by combining the forward bound with symmetry of
information at the same ambient scale. -/
theorem theorem35_backward
    {x rs fi fj : Program} {pre mid post : List Program}
    (hchain : IsIncrementalPrefixCompression x (pre ++ [fi] ++ mid ++ [fj] ++ post) rs) :
    StepLogLe (PrefixInformation fj fi) 0 (2 * mid.length + 4) (BitString.blen x) := by
  have hforward := theorem35_forward (x := x) (rs := rs)
    (fi := fi) (fj := fj) (pre := pre) (mid := mid) (post := post) hchain
  have hfiLen :
      BitString.blen fi ≤ BitString.blen x := by
    exact targetFeature_length_le_of_chain
      (x := x) (rs := rs) (f := fi) (gs := pre) (hs := mid ++ [fj] ++ post) <| by
        simpa [List.append_assoc] using hchain
  have hfjLen :
      BitString.blen fj ≤ BitString.blen x := by
    exact targetFeature_length_le_of_chain
      (x := x) (rs := rs) (f := fj) (gs := pre ++ [fi] ++ mid) (hs := post) <| by
        simpa [List.append_assoc] using hchain
  have hsymm :
      LogEq (PrefixInformation fj fi) (PrefixInformation fi fj) (BitString.blen x) := by
    exact prefixInformation_symm_of_lengthBounds hfjLen hfiLen
  have hfinal := stepLogLe_trans (stepLogLe_of_logLe hsymm.1) hforward
  have hs : 1 + (2 * mid.length + 3) = 2 * mid.length + 4 := by
    omega
  simpa [hs, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

/-- Split-form Theorem 3.5: in an incremental compression chain, two features separated by
`mid.length` intermediate steps carry only linearly many logarithmic-overhead steps of mutual
information, in both directions. -/
theorem theorem35_split
    {x rs fi fj : Program} {pre mid post : List Program}
    (hchain : IsIncrementalPrefixCompression x (pre ++ [fi] ++ mid ++ [fj] ++ post) rs) :
    StepLogLe (PrefixInformation fi fj) 0 (2 * mid.length + 4) (BitString.blen x) ∧
      StepLogLe (PrefixInformation fj fi) 0 (2 * mid.length + 4) (BitString.blen x) := by
  refine ⟨?_, theorem35_backward hchain⟩
  exact stepLogLe_of_stepCount_le (theorem35_forward hchain) (by omega)

private theorem incrementalCompression_index_split
    {x rs : Program} {fs : List Program} {i j : Nat}
    (hi : i < fs.length)
    (hj : j < fs.length)
    (hij : i < j)
    (hchain : IsIncrementalPrefixCompression x fs rs) :
    IsIncrementalPrefixCompression x
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
  have hrewritten : IsIncrementalPrefixCompression x
      (fs.take i ++ [fs[i]] ++ (fs.drop (i + 1)).take (j - i - 1) ++ [fs[j]] ++ fs.drop (j + 1))
      rs := by
    rw [← hsplit]
    exact hchain
  exact hrewritten

private theorem theorem35_of_ltIndices
    {x rs : Program} {fs : List Program} {i j : Nat}
    (hchain : IsIncrementalPrefixCompression x fs rs)
    (hi : i < fs.length)
    (hj : j < fs.length)
    (hij : i < j) :
    StepLogLe (PrefixInformation fs[i] fs[j]) 0 (2 * (j - i - 1) + 4) (BitString.blen x) ∧
      StepLogLe (PrefixInformation fs[j] fs[i]) 0 (2 * (j - i - 1) + 4) (BitString.blen x) := by
  have hmidLen : ((fs.drop (i + 1)).take (j - i - 1)).length = j - i - 1 := by
    simp [List.length_take, List.length_drop]
    omega
  simpa [hmidLen] using
    theorem35_split
      (x := x) (rs := rs) (fi := fs[i]) (fj := fs[j])
      (pre := fs.take i)
      (mid := (fs.drop (i + 1)).take (j - i - 1))
      (post := fs.drop (j + 1))
      (incrementalCompression_index_split hi hj hij hchain)

/-- Prefix-form Theorem 3.5 in index form. Two distinct features in an incremental compression
chain are pairwise orthogonal, with logarithmic overhead linear in their distance. This is the
current project-level formalization of `I(fi* : fj*) = O(|i - j| log l(x))`. -/
theorem theorem35
    {x rs : Program} {fs : List Program} {i j : Nat}
    (hchain : IsIncrementalPrefixCompression x fs rs)
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
      theorem35_of_ltIndices hchain hi hj hij'
    have hdist : Nat.dist i j = j - i := by
      exact Nat.dist_eq_sub_of_le hij'.le
    simpa [hdist] using hlt
  · have hlt :=
      theorem35_of_ltIndices hchain hj hi hij'
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
