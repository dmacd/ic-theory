import IcTheory.Compression.Section33

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- High-information features are incompressible in the paper's sense:
the feature length is bounded below by its prefix complexity up to logarithmic slack. -/
private theorem featureLength_logLe_prefixComplexity_of_highInformation {f x : Program}
    (hfeature : IsFeature runs f x)
    (hinfo : HighInformationIn f x) :
    LogLe (BitString.blen f) (PrefixComplexity f) (BitString.blen x) := by
  have hproj :
      LogLe (PrefixComplexity x) (JointComplexity f x) (BitString.blen x) := by
    exact logLe_of_scale_logLe
      (jointRightProjectionLogLe f x)
      (jointComplexity_featureObject_logLe_of_highInformation hfeature hinfo)
  have hupper :
      LogLe (JointComplexity f x)
        (PrefixComplexity f + PrefixConditionalComplexity x f)
        (BitString.blen x) :=
    jointUpperAtFeatureScale_of_highInformation hfeature hinfo
  have hkx :
      LogLe (PrefixComplexity x)
        (PrefixComplexity f + PrefixConditionalComplexity x f)
        (BitString.blen x) := by
    exact logLe_trans hproj hupper
  rcases hinfo with ⟨c₁, d₁, h₁⟩
  rcases hkx with ⟨c₂, d₂, h₂⟩
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  have hsum :
      BitString.blen f + PrefixConditionalComplexity x f ≤
        PrefixComplexity f + PrefixConditionalComplexity x f +
          (c₁ + c₂) * logPenalty (BitString.blen x) + (d₁ + d₂) := by
    calc
      BitString.blen f + PrefixConditionalComplexity x f ≤
          PrefixComplexity x + c₁ * logPenalty (BitString.blen x) + d₁ := h₁
      _ ≤
          PrefixComplexity f + PrefixConditionalComplexity x f +
            (c₂ * logPenalty (BitString.blen x) + d₂) +
            (c₁ * logPenalty (BitString.blen x) + d₁) := by
        omega
      _ =
          PrefixComplexity f + PrefixConditionalComplexity x f +
            (c₁ + c₂) * logPenalty (BitString.blen x) + (d₁ + d₂) := by
        rw [Nat.add_mul]
        omega
  omega

/-- Theorem 3.1 in the prefix-incompressible branch:
high information forces a shortest feature to be prefix-incompressible up to logarithmic slack. -/
theorem theorem31_of_prefixGap {f x : Program}
    (hshort : IsShortestFeature runs f x)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    LogEq (PrefixComplexity f) (BitString.blen f) (BitString.blen x) := by
  let hfeature : IsFeature runs f x := shortestFeature_isFeature hshort
  have hlen : BitString.blen f ≤ BitString.blen x := (feature_length_lt hfeature).le
  have hinfo : HighInformationIn f x := by
    rcases hfeature with ⟨g, r, hg, hf, hcomp⟩
    rcases lemma32_log hf hcomp with ⟨c₁, d₁, h₁⟩
    rcases hgap with ⟨c₂, d₂, h₂⟩
    refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
    have hsum :
        BitString.blen f + PrefixConditionalComplexity x f ≤
          BitString.blen x + (c₁ * logPenalty (BitString.blen x) + d₁) := by
      omega
    have hsum' :
        BitString.blen f + PrefixConditionalComplexity x f ≤
          PrefixComplexity x + (c₂ * logPenalty (BitString.blen x) + d₂) +
            (c₁ * logPenalty (BitString.blen x) + d₁) := by
      omega
    simpa [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum'
  refine ⟨prefixComplexity_log_upper_of_le hlen, ?_⟩
  exact featureLength_logLe_prefixComplexity_of_highInformation hfeature hinfo

/-- Theorem 3.1 in the highly-compressible branch:
all shortest features already live in a constant-size family, so incompressibility is automatic. -/
theorem theorem31_of_compressibleByMoreThan {f x : Program}
    (hshort : IsShortestFeature runs f x)
    (hcompress : CompressibleByMoreThan universalFeatureConstant x) :
    LogEq (PrefixComplexity f) (BitString.blen f) (BitString.blen x) := by
  let hfeature : IsFeature runs f x := shortestFeature_isFeature hshort
  have hlenx : BitString.blen f ≤ BitString.blen x := (feature_length_lt hfeature).le
  have hconst : BitString.blen f ≤ universalFeatureConstant :=
    shortestFeature_le_universalFeatureConstant hshort hcompress
  refine ⟨prefixComplexity_log_upper_of_le hlenx, ?_⟩
  refine ⟨0, universalFeatureConstant, ?_⟩
  omega

/-- Theorem 3.1 packaged by the two Section 3.1 branches currently formalized in the repo. -/
theorem theorem31_of_cases {f x : Program}
    (hshort : IsShortestFeature runs f x)
    (hcases : CompressibleByMoreThan universalFeatureConstant x ∨
      LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    LogEq (PrefixComplexity f) (BitString.blen f) (BitString.blen x) := by
  rcases hcases with hcompress | hgap
  · exact theorem31_of_compressibleByMoreThan hshort hcompress
  · exact theorem31_of_prefixGap hshort hgap

/-- If `x` is prefix-incompressible up to logarithmic slack, then every feature of `x` carries
high information in the sense needed for Lemma 3.3. -/
theorem highInformationIn_of_feature_of_prefixGap {f x : Program}
    (hfeature : IsFeature runs f x)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    HighInformationIn f x := by
  rcases hfeature with ⟨g, r, hg, hf, hcomp⟩
  have hlen : BitString.blen f ≤ BitString.blen x := (feature_length_lt ⟨g, ⟨r, hg, hf, hcomp⟩⟩).le
  rcases lemma32_log hf hcomp with ⟨c₁, d₁, h₁⟩
  rcases hgap with ⟨c₂, d₂, h₂⟩
  refine ⟨c₁ + c₂, d₁ + d₂, ?_⟩
  have hsum :
      BitString.blen f + PrefixConditionalComplexity x f ≤
        BitString.blen x + (c₁ * logPenalty (BitString.blen x) + d₁) := by
    omega
  have hsum' :
      BitString.blen f + PrefixConditionalComplexity x f ≤
        PrefixComplexity x + (c₂ * logPenalty (BitString.blen x) + d₂) +
          (c₁ * logPenalty (BitString.blen x) + d₁) := by
    omega
  simpa [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum'

/-- Under the prefix-gap hypothesis, every shortest feature has only logarithmic conditional
prefix complexity relative to `x`. -/
theorem shortestFeature_conditionalPrefixLogLe_of_prefixGap {f x : Program}
    (hshort : IsShortestFeature runs f x)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  let hfeature : IsFeature runs f x := shortestFeature_isFeature hshort
  exact lemma33 hfeature (highInformationIn_of_feature_of_prefixGap hfeature hgap)

/-- In the highly-compressible branch of Theorem 3.2, shortest features are bounded by the fixed
universal-feature constant, hence have constant-size conditional prefix descriptions. -/
theorem shortestFeature_conditionalPrefixLogLe_of_compressibleByMoreThan {f x : Program}
    (hshort : IsShortestFeature runs f x)
    (hcompress : CompressibleByMoreThan universalFeatureConstant x) :
    LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x) := by
  have hlen : BitString.blen f ≤ universalFeatureConstant :=
    shortestFeature_le_universalFeatureConstant hshort hcompress
  have hprefix := prefixConditionalComplexity_le_rightPayload f x
  have hmono :
      BitString.blen (BitString.ofNat (BitString.blen f)) ≤
        BitString.blen (BitString.ofNat universalFeatureConstant) := BitString.blen_ofNat_mono hlen
  have hconst :
      PrefixConditionalComplexity f x ≤
        universalFeatureConstant + 2 * BitString.blen (BitString.ofNat universalFeatureConstant) +
          rightInterpreterPrefixOverhead := by
    exact le_trans hprefix (by omega)
  refine ⟨0,
    universalFeatureConstant + 2 * BitString.blen (BitString.ofNat universalFeatureConstant) +
      rightInterpreterPrefixOverhead, ?_⟩
  simpa using hconst

private noncomputable def shortestFeatureCompressibleCandidates (x : Program) : Finset Program :=
  by
    classical
    exact ((BitString.allUpToLength universalFeatureConstant).toFinset).filter
      (fun f : Program => decide (IsShortestFeature runs f x))

/-- Canonical list of shortest features in the highly-compressible branch. -/
noncomputable def shortestFeaturesOfCompressibleByMoreThan (x : Program) : List Program :=
  (shortestFeatureCompressibleCandidates x).toList

theorem mem_shortestFeaturesOfCompressibleByMoreThan_iff {f x : Program}
    (hcompress : CompressibleByMoreThan universalFeatureConstant x) :
    f ∈ shortestFeaturesOfCompressibleByMoreThan x ↔ IsShortestFeature runs f x := by
  classical
  constructor
  · intro hf
    unfold shortestFeaturesOfCompressibleByMoreThan shortestFeatureCompressibleCandidates at hf
    rw [Finset.mem_toList] at hf
    simpa using (Finset.mem_filter.mp hf).2
  · intro hshort
    unfold shortestFeaturesOfCompressibleByMoreThan shortestFeatureCompressibleCandidates
    rw [Finset.mem_toList]
    refine Finset.mem_filter.mpr ⟨?_, by simpa using hshort⟩
    exact List.mem_toFinset.mpr <|
      (BitString.mem_allUpToLength_iff.2
        (shortestFeature_le_universalFeatureConstant hshort hcompress))

theorem nodup_shortestFeaturesOfCompressibleByMoreThan (x : Program) :
    (shortestFeaturesOfCompressibleByMoreThan x).Nodup := by
  classical
  simpa [shortestFeaturesOfCompressibleByMoreThan] using
    (shortestFeatureCompressibleCandidates x).nodup_toList

theorem length_shortestFeaturesOfCompressibleByMoreThan_le (x : Program) :
    (shortestFeaturesOfCompressibleByMoreThan x).length ≤
      2 ^ (universalFeatureConstant + 1) - 1 := by
  classical
  unfold shortestFeaturesOfCompressibleByMoreThan
  calc
    (shortestFeatureCompressibleCandidates x).toList.length =
        (shortestFeatureCompressibleCandidates x).card := by
          simp
    _ ≤ ((BitString.allUpToLength universalFeatureConstant).toFinset).card := by
          exact Finset.card_filter_le
            ((BitString.allUpToLength universalFeatureConstant).toFinset)
            (fun f : Program => decide (IsShortestFeature runs f x))
    _ ≤ (BitString.allUpToLength universalFeatureConstant).length := by
          exact List.toFinset_card_le _
    _ = 2 ^ (universalFeatureConstant + 1) - 1 := by
          simp

/-- The highly-compressible branch of Theorem 3.2: shortest features live in a constant-size
family and have constant-size conditional prefix descriptions. -/
theorem theorem32_of_compressibleByMoreThan {x : Program}
    (hcompress : CompressibleByMoreThan universalFeatureConstant x) :
    (∀ f : Program, IsShortestFeature runs f x →
      LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x)) ∧
    ∃ L : List Program,
      L.Nodup ∧
      (∀ f : Program, f ∈ L ↔ IsShortestFeature runs f x) ∧
      L.length ≤ 2 ^ (universalFeatureConstant + 1) - 1 := by
  refine ⟨?_, ?_⟩
  · intro f hshort
    exact shortestFeature_conditionalPrefixLogLe_of_compressibleByMoreThan hshort hcompress
  · refine ⟨shortestFeaturesOfCompressibleByMoreThan x,
      nodup_shortestFeaturesOfCompressibleByMoreThan x, ?_, ?_⟩
    · intro f
      exact mem_shortestFeaturesOfCompressibleByMoreThan_iff hcompress
    · exact length_shortestFeaturesOfCompressibleByMoreThan_le x

private noncomputable def shortestFeatureCandidates (x : Program) : Finset Program :=
  (BitString.allUpToLength (BitString.blen x)).toFinset

private theorem mem_shortestFeatureCandidates_of_shortestFeature {f x : Program}
    (hshort : IsShortestFeature runs f x) :
    f ∈ shortestFeatureCandidates x := by
  exact List.mem_toFinset.mpr
    ((BitString.mem_allUpToLength_iff).2
      ((feature_length_lt (shortestFeature_isFeature hshort)).le))

private noncomputable def shortestFeaturePrefixCondBoundPair
    (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x))
    (f : Program) : Nat × Nat := by
  classical
  exact if h : IsShortestFeature runs f x then
    let hc := Classical.choose (shortestFeature_conditionalPrefixLogLe_of_prefixGap h hgap)
    let hd := Classical.choose (Classical.choose_spec
      (shortestFeature_conditionalPrefixLogLe_of_prefixGap h hgap))
    (hc, hd)
  else
    (0, 0)

private theorem shortestFeaturePrefixCondBoundPair_spec {f x : Program}
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x))
    (hshort : IsShortestFeature runs f x) :
    PrefixConditionalComplexity f x ≤
      (shortestFeaturePrefixCondBoundPair x hgap f).1 * logPenalty (BitString.blen x) +
        (shortestFeaturePrefixCondBoundPair x hgap f).2 := by
  classical
  simpa [shortestFeaturePrefixCondBoundPair, hshort] using
    (Classical.choose_spec
      (Classical.choose_spec (shortestFeature_conditionalPrefixLogLe_of_prefixGap hshort hgap)))

noncomputable def shortestFeaturePrefixCondBoundC
    (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) : Nat :=
  (shortestFeatureCandidates x).sup
    (fun f : Program => (shortestFeaturePrefixCondBoundPair x hgap f).1)

noncomputable def shortestFeaturePrefixCondBoundD
    (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) : Nat :=
  (shortestFeatureCandidates x).sup
    (fun f : Program => (shortestFeaturePrefixCondBoundPair x hgap f).2)

/-- Uniform logarithmic budget for conditional prefix descriptions of shortest features under the
prefix-gap hypothesis. -/
noncomputable def shortestFeaturePrefixBudget
    (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) : Nat :=
  shortestFeaturePrefixCondBoundC x hgap * logPenalty (BitString.blen x) +
    shortestFeaturePrefixCondBoundD x hgap

theorem shortestFeature_conditionalPrefixComplexity_le_budget_of_prefixGap {f x : Program}
    (hshort : IsShortestFeature runs f x)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    PrefixConditionalComplexity f x ≤ shortestFeaturePrefixBudget x hgap := by
  have hspec := shortestFeaturePrefixCondBoundPair_spec (x := x) hgap hshort
  have hmem : f ∈ shortestFeatureCandidates x :=
    mem_shortestFeatureCandidates_of_shortestFeature hshort
  have hc :
      (shortestFeaturePrefixCondBoundPair x hgap f).1 ≤
        shortestFeaturePrefixCondBoundC x hgap := by
    exact Finset.le_sup
      (f := fun g : Program => (shortestFeaturePrefixCondBoundPair x hgap g).1) hmem
  have hd :
      (shortestFeaturePrefixCondBoundPair x hgap f).2 ≤
        shortestFeaturePrefixCondBoundD x hgap := by
    exact Finset.le_sup
      (f := fun g : Program => (shortestFeaturePrefixCondBoundPair x hgap g).2) hmem
  unfold shortestFeaturePrefixBudget
  have hcmul :
      (shortestFeaturePrefixCondBoundPair x hgap f).1 * logPenalty (BitString.blen x) ≤
        shortestFeaturePrefixCondBoundC x hgap * logPenalty (BitString.blen x) := by
    exact Nat.mul_le_mul_right _ hc
  calc
    PrefixConditionalComplexity f x ≤
        (shortestFeaturePrefixCondBoundPair x hgap f).1 * logPenalty (BitString.blen x) +
          (shortestFeaturePrefixCondBoundPair x hgap f).2 := hspec
    _ ≤ shortestFeaturePrefixCondBoundC x hgap * logPenalty (BitString.blen x) +
          shortestFeaturePrefixCondBoundD x hgap := by
        exact Nat.add_le_add hcmul hd

/-- Canonical list of shortest features, extracted from the bounded family of short conditional
prefix descriptions guaranteed by the prefix-gap hypothesis. -/
noncomputable def shortestFeaturesOfPrefixGap
    (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) : List Program := by
  classical
  exact (prefixOutputsUpToLength x (shortestFeaturePrefixBudget x hgap)).filter
    fun f => decide (IsShortestFeature runs f x)

theorem mem_shortestFeaturesOfPrefixGap_iff {f x : Program}
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    f ∈ shortestFeaturesOfPrefixGap x hgap ↔ IsShortestFeature runs f x := by
  constructor
  · intro hf
    unfold shortestFeaturesOfPrefixGap at hf
    simpa using (List.mem_filter.1 hf).2
  · intro hshort
    unfold shortestFeaturesOfPrefixGap
    refine List.mem_filter.2 ⟨?_, by simpa using hshort⟩
    exact mem_prefixOutputsUpToLength_of_prefixConditionalComplexity_le
      (shortestFeature_conditionalPrefixComplexity_le_budget_of_prefixGap hshort hgap)

theorem nodup_shortestFeaturesOfPrefixGap (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    (shortestFeaturesOfPrefixGap x hgap).Nodup := by
  unfold shortestFeaturesOfPrefixGap
  exact (nodup_prefixOutputsUpToLength x (shortestFeaturePrefixBudget x hgap)).filter _

theorem length_shortestFeaturesOfPrefixGap_le (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    (shortestFeaturesOfPrefixGap x hgap).length ≤
      2 ^ (shortestFeaturePrefixBudget x hgap + 1) - 1 := by
  classical
  unfold shortestFeaturesOfPrefixGap
  exact le_trans
    (List.length_filter_le (l := prefixOutputsUpToLength x (shortestFeaturePrefixBudget x hgap))
      (p := fun f => decide (IsShortestFeature runs f x)))
    (length_prefixOutputsUpToLength_le x (shortestFeaturePrefixBudget x hgap))

private theorem two_pow_shortestFeatureBudget_succ_le_poly (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    2 ^ (shortestFeaturePrefixBudget x hgap + 1) ≤
      (BitString.blen x + 1) ^ (shortestFeaturePrefixCondBoundC x hgap) *
        2 ^ (shortestFeaturePrefixCondBoundD x hgap + 1) := by
  let n := BitString.blen x
  let c := shortestFeaturePrefixCondBoundC x hgap
  let d := shortestFeaturePrefixCondBoundD x hgap
  have hlog : 2 ^ logPenalty n ≤ n + 1 := by
    unfold logPenalty
    simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  unfold shortestFeaturePrefixBudget
  calc
    2 ^ (c * logPenalty n + d + 1) =
        2 ^ (c * logPenalty n) * 2 ^ (d + 1) := by
          rw [show c * logPenalty n + d + 1 = c * logPenalty n + (d + 1) by omega, Nat.pow_add]
    _ = (2 ^ logPenalty n) ^ c * 2 ^ (d + 1) := by
      rw [show c * logPenalty n = logPenalty n * c by rw [Nat.mul_comm], Nat.pow_mul]
    _ ≤ (n + 1) ^ c * 2 ^ (d + 1) := by
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlog c)

/-- Polynomial bound on the canonical list of shortest features under the prefix-gap hypothesis. -/
theorem length_shortestFeaturesOfPrefixGap_poly_le (x : Program)
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    (shortestFeaturesOfPrefixGap x hgap).length ≤
      (BitString.blen x + 1) ^ (shortestFeaturePrefixCondBoundC x hgap) *
        2 ^ (shortestFeaturePrefixCondBoundD x hgap + 1) := by
  exact le_trans (length_shortestFeaturesOfPrefixGap_le x hgap)
    (le_trans (Nat.sub_le _ _) (two_pow_shortestFeatureBudget_succ_le_poly x hgap))

/-- The nontrivial branch of Theorem 3.2: if `x` is prefix-incompressible up to logarithmic slack,
then shortest features have logarithmic conditional prefix complexity, and they lie in a list of
polynomially bounded size. -/
theorem theorem32_of_prefixGap {x : Program}
    (hgap : LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    (∀ f : Program, IsShortestFeature runs f x →
      LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x)) ∧
    ∃ L : List Program,
      L.Nodup ∧
      (∀ f : Program, f ∈ L ↔ IsShortestFeature runs f x) ∧
      L.length ≤
        (BitString.blen x + 1) ^ (shortestFeaturePrefixCondBoundC x hgap) *
          2 ^ (shortestFeaturePrefixCondBoundD x hgap + 1) := by
  refine ⟨?_, ?_⟩
  · intro f hshort
    exact shortestFeature_conditionalPrefixLogLe_of_prefixGap hshort hgap
  · refine ⟨shortestFeaturesOfPrefixGap x hgap, nodup_shortestFeaturesOfPrefixGap x hgap, ?_, ?_⟩
    · intro f
      exact mem_shortestFeaturesOfPrefixGap_iff hgap
    · exact length_shortestFeaturesOfPrefixGap_poly_le x hgap

/-- Theorem 3.2 packaged by cases. The current development covers the two branches separately:
the universal-feature branch for strings compressible past the fixed threshold, and the
prefix-incompressible branch handled through Lemma 3.3. -/
theorem theorem32_of_cases {x : Program}
    (hcases : CompressibleByMoreThan universalFeatureConstant x ∨
      LogLe (BitString.blen x) (PrefixComplexity x) (BitString.blen x)) :
    (∀ f : Program, IsShortestFeature runs f x →
      LogLe (PrefixConditionalComplexity f x) 0 (BitString.blen x)) ∧
    ∃ L : List Program, ∃ α β : Nat,
      L.Nodup ∧
      (∀ f : Program, f ∈ L ↔ IsShortestFeature runs f x) ∧
      L.length ≤ (BitString.blen x + 1) ^ α * β := by
  rcases hcases with hcompress | hgap
  · rcases theorem32_of_compressibleByMoreThan (x := x) hcompress with ⟨hK, L, hnodup, hmem, hlen⟩
    refine ⟨hK, L, 0, 2 ^ (universalFeatureConstant + 1) - 1, hnodup, hmem, ?_⟩
    simpa using hlen
  · rcases theorem32_of_prefixGap (x := x) hgap with ⟨hK, L, hnodup, hmem, hlen⟩
    refine ⟨hK, L, shortestFeaturePrefixCondBoundC x hgap,
      2 ^ (shortestFeaturePrefixCondBoundD x hgap + 1), hnodup, hmem, ?_⟩
    simpa using hlen

end

end Compression

end IcTheory
