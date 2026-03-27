import IcTheory.Computability.FinitePrefixDescriptions
import IcTheory.Basics.FiniteBitStrings
import IcTheory.Compression.Feature
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

/-- Project-style lower semicomputability: a monotone computable approximation which stabilizes to
the target value on every input. -/
def IsLowerSemicomputable (δ : Program → Nat) : Prop :=
  ∃ φ : Nat → Program → Nat,
    Computable (fun a : Nat × Program => φ a.1 a.2) ∧
    (∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x) ∧
    ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x

/-- Strings of fixed length `n` on which the test value is at least `m`. -/
def randomnessLevelSet (δ : Program → Nat) (n m : Nat) : List Program :=
  (BitString.allOfLength n).filter (fun x => decide (m ≤ δ x))

@[simp] theorem mem_randomnessLevelSet_iff {δ : Program → Nat} {x : Program} {n m : Nat} :
    x ∈ randomnessLevelSet δ n m ↔ BitString.blen x = n ∧ m ≤ δ x := by
  simp [randomnessLevelSet]

@[simp] theorem nodup_randomnessLevelSet (δ : Program → Nat) (n m : Nat) :
    (randomnessLevelSet δ n m).Nodup := by
  unfold randomnessLevelSet
  exact (BitString.nodup_allOfLength n).filter _

/-- Project-style Martin-Löf test: lower semicomputable with the usual uniform level-set bound. -/
structure IsUniformMartinLofTest (δ : Program → Nat) : Prop where
  lowerSemicomputable : IsLowerSemicomputable δ
  levelBound : ∀ n m, (randomnessLevelSet δ n m).length ≤ 2 ^ (n - m)

/-- Exact per-residual deficiency contribution of a fixed plain program `f` on input `x`. -/
noncomputable def featureDeficiencyCandidate (f x r : Program) : Nat := by
  classical
  exact
    if hlt : BitString.blen f + BitString.blen r < BitString.blen x then
      if runs f r x then BitString.blen x - BitString.blen r - 1 else 0
    else 0

/-- Fuel-bounded approximation to `featureDeficiencyCandidate`. -/
def featureDeficiencyApproxCandidate (f : Program) (t : Nat) (x r : Program) : Nat :=
  if hlt : BitString.blen f + BitString.blen r < BitString.blen x then
    if prefixOutputAtFuel t f r = some x then BitString.blen x - BitString.blen r - 1 else 0
  else 0

/-- The randomness test induced by a fixed plain program `f`, matching equation (57). -/
noncomputable def featureRandomnessTest (f x : Program) : Nat :=
  ((BitString.allUpToLength (BitString.blen x)).map (featureDeficiencyCandidate f x)).foldl max 0

/-- Fuel-bounded approximation to `featureRandomnessTest`. -/
def featureRandomnessApprox (f : Program) (t : Nat) (x : Program) : Nat :=
  ((BitString.allUpToLength (BitString.blen x)).map (featureDeficiencyApproxCandidate f t x)).foldl max 0

theorem prefixOutputAtFuel_mono {k₁ k₂ : Nat} {p input output : Program}
    (hk : k₁ ≤ k₂)
    (h : prefixOutputAtFuel k₁ p input = some output) :
    prefixOutputAtFuel k₂ p input = some output := by
  rw [prefixOutputAtFuel, Option.map_eq_some_iff] at h ⊢
  rcases h with ⟨outputNat, hk1, rfl⟩
  exact ⟨outputNat, Nat.Partrec.Code.evaln_mono hk hk1, rfl⟩

private theorem foldl_max_eq_max_foldl (l : List Nat) (a : Nat) :
    l.foldl max a = max a (l.foldl max 0) := by
  induction l generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (max a x), show max 0 x = x by simp, ih x]
      simp [max_assoc, max_left_comm, max_comm]

private theorem exists_mem_of_foldl_max_ge {l : List Nat} {m : Nat}
    (hm : 0 < m)
    (h : m ≤ l.foldl max 0) :
    ∃ a ∈ l, m ≤ a := by
  induction l with
  | nil =>
      exfalso
      have hm0 : m = 0 := by simpa using h
      omega
  | cons a l ih =>
      have hmax : l.foldl max a = max a (l.foldl max 0) := foldl_max_eq_max_foldl l a
      simp [List.foldl_cons, hmax] at h ⊢
      by_cases ha : m ≤ a
      · exact Or.inl ha
      · have hl : m ≤ l.foldl max 0 := by omega
        exact Or.inr (ih hl)

private theorem foldl_max_map_le_of_pointwise_aux {α : Type} (l : List α) (f g : α → Nat)
    {a b : Nat} (hab : a ≤ b)
    (hfg : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).foldl max a ≤ (l.map g).foldl max b := by
  induction l generalizing a b with
  | nil =>
      simpa using hab
  | cons x xs ih =>
      simp
      apply ih
      · exact max_le_max hab (hfg x (by simp))
      · intro y hy
        exact hfg y (by simp [hy])

private theorem foldl_max_map_le_of_pointwise {α : Type} (l : List α) (f g : α → Nat)
    (hfg : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).foldl max 0 ≤ (l.map g).foldl max 0 := by
  exact foldl_max_map_le_of_pointwise_aux l f g (a := 0) (b := 0) (le_rfl) hfg

private theorem foldl_max_map_eq_of_pointwise_aux {α : Type} (l : List α) (f g : α → Nat)
    {a : Nat} (hfg : ∀ x ∈ l, f x = g x) :
    (l.map f).foldl max a = (l.map g).foldl max a := by
  induction l generalizing a with
  | nil =>
      simp
  | cons x xs ih =>
      simp [hfg x (by simp), ih (by intro y hy; exact hfg y (by simp [hy]))]

private theorem foldl_max_map_eq_of_pointwise {α : Type} (l : List α) (f g : α → Nat)
    (hfg : ∀ a ∈ l, f a = g a) :
    (l.map f).foldl max 0 = (l.map g).foldl max 0 := by
  exact foldl_max_map_eq_of_pointwise_aux l f g (a := 0) hfg

theorem featureDeficiencyApproxCandidate_mono {f : Program} {t₁ t₂ : Nat} {x r : Program}
    (ht : t₁ ≤ t₂) :
    featureDeficiencyApproxCandidate f t₁ x r ≤ featureDeficiencyApproxCandidate f t₂ x r := by
  unfold featureDeficiencyApproxCandidate
  by_cases hlt : BitString.blen f + BitString.blen r < BitString.blen x
  · by_cases h1 : prefixOutputAtFuel t₁ f r = some x
    · have h2 : prefixOutputAtFuel t₂ f r = some x := prefixOutputAtFuel_mono ht h1
      simp [hlt, h1, h2]
    · simp [hlt, h1]
  · simp [hlt]

theorem featureDeficiencyApproxCandidate_eventually_eq (f x r : Program) :
    ∃ T, ∀ {t}, T ≤ t →
      featureDeficiencyApproxCandidate f t x r = featureDeficiencyCandidate f x r := by
  unfold featureDeficiencyCandidate featureDeficiencyApproxCandidate
  by_cases hlt : BitString.blen f + BitString.blen r < BitString.blen x
  · by_cases hrun : runs f r x
    · rcases prefixOutputAtFuel_complete hrun with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      intro t ht
      have hkt : prefixOutputAtFuel t f r = some x := prefixOutputAtFuel_mono ht hk
      simp [hlt, hrun, hkt]
    · refine ⟨0, ?_⟩
      intro t ht
      by_cases hpf : prefixOutputAtFuel t f r = some x
      · have hrun : runs f r x := prefixOutputAtFuel_sound hpf
        contradiction
      · simp [hlt, hrun, hpf]
  · refine ⟨0, ?_⟩
    intro t ht
    simp [hlt]

theorem featureRandomnessApprox_mono {f : Program} {t₁ t₂ : Nat} {x : Program}
    (ht : t₁ ≤ t₂) :
    featureRandomnessApprox f t₁ x ≤ featureRandomnessApprox f t₂ x := by
  unfold featureRandomnessApprox
  exact foldl_max_map_le_of_pointwise _ _ _
    (by
      intro r hr
      exact featureDeficiencyApproxCandidate_mono ht)

private theorem featureRandomnessApprox_eventually_eq_on_list
    (f x : Program) (residuals : List Program)
    (hres :
      ∀ r ∈ residuals, ∃ T, ∀ {t}, T ≤ t →
        featureDeficiencyApproxCandidate f t x r = featureDeficiencyCandidate f x r) :
    ∃ T, ∀ {t}, T ≤ t →
      (residuals.map (featureDeficiencyApproxCandidate f t x)).foldl max 0 =
        (residuals.map (featureDeficiencyCandidate f x)).foldl max 0 := by
  induction residuals with
  | nil =>
      refine ⟨0, ?_⟩
      intro t ht
      simp
  | cons r rs ih =>
      rcases hres r (by simp) with ⟨Tr, hTr⟩
      have hrs :
          ∀ s ∈ rs, ∃ T, ∀ {t}, T ≤ t →
            featureDeficiencyApproxCandidate f t x s = featureDeficiencyCandidate f x s := by
        intro s hs
        exact hres s (by simp [hs])
      rcases ih hrs with ⟨Ts, hTs⟩
      refine ⟨max Tr Ts, ?_⟩
      intro t ht
      have hrEq :
          featureDeficiencyApproxCandidate f t x r = featureDeficiencyCandidate f x r := by
        exact hTr (le_trans (le_max_left _ _) ht)
      have hsEq :
          (rs.map (featureDeficiencyApproxCandidate f t x)).foldl max 0 =
            (rs.map (featureDeficiencyCandidate f x)).foldl max 0 := by
        exact hTs (le_trans (le_max_right _ _) ht)
      have htail :
          (rs.map (featureDeficiencyApproxCandidate f t x)).foldl max
              (featureDeficiencyCandidate f x r) =
            (rs.map (featureDeficiencyCandidate f x)).foldl max
              (featureDeficiencyCandidate f x r) := by
        calc
          (rs.map (featureDeficiencyApproxCandidate f t x)).foldl max
              (featureDeficiencyCandidate f x r) =
              max (featureDeficiencyCandidate f x r)
                ((rs.map (featureDeficiencyApproxCandidate f t x)).foldl max 0) := by
                  exact foldl_max_eq_max_foldl _ _
          _ = max (featureDeficiencyCandidate f x r)
                ((rs.map (featureDeficiencyCandidate f x)).foldl max 0) := by
                  rw [hsEq]
          _ =
              (rs.map (featureDeficiencyCandidate f x)).foldl max
                (featureDeficiencyCandidate f x r) := by
                  exact (foldl_max_eq_max_foldl _ _).symm
      simpa [List.map_cons, List.foldl_cons, hrEq] using htail

theorem featureRandomnessApprox_eventually_eq (f x : Program) :
    ∃ T, ∀ {t}, T ≤ t → featureRandomnessApprox f t x = featureRandomnessTest f x := by
  let residuals := BitString.allUpToLength (BitString.blen x)
  have hres :
      ∀ r ∈ residuals, ∃ T, ∀ {t}, T ≤ t →
        featureDeficiencyApproxCandidate f t x r = featureDeficiencyCandidate f x r := by
    intro r hr
    exact featureDeficiencyApproxCandidate_eventually_eq f x r
  rcases featureRandomnessApprox_eventually_eq_on_list f x residuals hres with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  simpa [featureRandomnessApprox, featureRandomnessTest, residuals] using hT ht

private theorem allOfLength_primrec : Primrec BitString.allOfLength := by
  have hstep : Primrec₂ fun (_ : Nat) (xs : List Program) =>
      xs.map (List.cons false) ++ xs.map (List.cons true) := by
    have hmapFalse : Primrec fun p : Nat × List Program => p.2.map (List.cons false) := by
      exact Primrec.list_map Primrec.snd
        ((Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)
    have hmapTrue : Primrec fun p : Nat × List Program => p.2.map (List.cons true) := by
      exact Primrec.list_map Primrec.snd
        ((Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)
    exact (Primrec.list_append.comp hmapFalse hmapTrue).to₂
  refine (Primrec.nat_rec₁ ([[]] : List Program) hstep).of_eq ?_
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [BitString.allOfLength, ih]

private theorem allUpToLength_primrec : Primrec BitString.allUpToLength := by
  have hstep : Primrec₂ fun n (xs : List Program) =>
      xs ++ BitString.allOfLength (n + 1) := by
    exact (Primrec.list_append.comp
      Primrec.snd
      (allOfLength_primrec.comp (Primrec.succ.comp Primrec.fst))).to₂
  refine (Primrec.nat_rec₁ (BitString.allOfLength 0) hstep).of_eq ?_
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [BitString.allUpToLength, ih]

private theorem prefixOutputAtFuel_primrec :
    Primrec fun a : Nat × Program × Program =>
      prefixOutputAtFuel a.1 a.2.1 a.2.2 := by
  have hEvaln :
      Primrec fun a : Nat × Program × Program =>
        Nat.Partrec.Code.evaln a.1 (programToCode a.2.1) (BitString.toNatExact a.2.2) := by
    refine Nat.Partrec.Code.primrec_evaln.comp <|
      (show Primrec fun a : Nat × Program × Program =>
        ((a.1, programToCode a.2.1), BitString.toNatExact a.2.2) from ?_)
    refine Primrec.pair ?_ (BitString.toNatExact_primrec.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec.pair Primrec.fst
      ((Primrec.ofNat Nat.Partrec.Code).comp
        (BitString.toNatExact_primrec.comp (Primrec.fst.comp Primrec.snd)))
  exact (Primrec.option_map hEvaln
    ((BitString.ofNatExact_primrec.comp Primrec.snd).to₂)).of_eq fun a => by
      cases a with
      | mk k rest =>
          cases rest with
          | mk p input =>
              rfl

private theorem featureDeficiencyApproxCandidate_primrec :
    Primrec fun a : Nat × Program × Program × Program =>
      featureDeficiencyApproxCandidate a.2.1 a.1 a.2.2.1 a.2.2.2 := by
  have hlenF : Primrec fun a : Nat × Program × Program × Program => BitString.blen a.2.1 := by
    exact Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
  have hlenX : Primrec fun a : Nat × Program × Program × Program => BitString.blen a.2.2.1 := by
    exact Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hlenR : Primrec fun a : Nat × Program × Program × Program => BitString.blen a.2.2.2 := by
    exact Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hlt : PrimrecPred fun a : Nat × Program × Program × Program =>
      BitString.blen a.2.1 + BitString.blen a.2.2.2 < BitString.blen a.2.2.1 := by
    exact Primrec.nat_lt.comp (Primrec.nat_add.comp hlenF hlenR) hlenX
  have hvalue : Primrec fun a : Nat × Program × Program × Program =>
      BitString.blen a.2.2.1 - BitString.blen a.2.2.2 - 1 := by
    exact (Primrec.nat_sub.comp
      (Primrec.nat_sub.comp hlenX hlenR)
      (Primrec.const 1))
  have hprefixArg : Primrec fun a : Nat × Program × Program × Program =>
      (a.1, a.2.1, a.2.2.2) := by
    exact Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hprefix :
      Primrec fun a : Nat × Program × Program × Program =>
        prefixOutputAtFuel a.1 a.2.1 a.2.2.2 := by
    exact prefixOutputAtFuel_primrec.comp hprefixArg
  have hsomeX :
      Primrec fun a : Nat × Program × Program × Program => some a.2.2.1 := by
    exact Primrec.option_some.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hsame : PrimrecPred fun a : Nat × Program × Program × Program =>
      prefixOutputAtFuel a.1 a.2.1 a.2.2.2 = some a.2.2.1 := by
    exact Primrec.eq.comp hprefix hsomeX
  exact Primrec.ite hlt
    (Primrec.ite hsame hvalue (Primrec.const 0))
    (Primrec.const 0)

private theorem featureRandomnessApprox_primrec :
    Primrec fun a : Nat × Program × Program =>
      featureRandomnessApprox a.2.1 a.1 a.2.2 := by
  have hlist : Primrec fun a : Nat × Program × Program =>
      BitString.allUpToLength (BitString.blen a.2.2) := by
    exact allUpToLength_primrec.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have hstep :
      Primrec₂ fun a : Nat × Program × Program => fun p : Nat × Program =>
        max p.1 (featureDeficiencyApproxCandidate a.2.1 a.1 a.2.2 p.2) := by
    have harg : Primrec fun q : (Nat × Program × Program) × Nat × Program =>
        (q.1.1, q.1.2.1, q.1.2.2, q.2.2) := by
      exact Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.snd.comp Primrec.snd)))
    exact Primrec.nat_max.comp
      (Primrec.fst.comp Primrec.snd)
      (featureDeficiencyApproxCandidate_primrec.comp harg)
  refine (Primrec.list_foldl hlist (Primrec.const 0) hstep).of_eq ?_
  intro a
  cases a with
  | mk t rest =>
      cases rest with
      | mk f x =>
          simp [featureRandomnessApprox, List.foldl_map]

private theorem featureRandomnessApprox_computable (f : Program) :
    Computable fun a : Nat × Program =>
      featureRandomnessApprox f a.1 a.2 := by
  have harg : Primrec fun a : Nat × Program => (a.1, f, a.2) := by
    exact Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.const f) Primrec.snd)
  exact (featureRandomnessApprox_primrec.comp harg).to_comp

theorem featureRandomnessTest_lowerSemicomputable (f : Program) :
    IsLowerSemicomputable (featureRandomnessTest f) := by
  refine ⟨featureRandomnessApprox f, featureRandomnessApprox_computable f, ?_, ?_⟩
  · intro t₁ t₂ x ht
    exact featureRandomnessApprox_mono ht
  · intro x
    rcases featureRandomnessApprox_eventually_eq f x with ⟨T, hT⟩
    exact ⟨T, by intro t ht; exact hT ht⟩

theorem featureDeficiencyCandidate_ge {f x r : Program} {m : Nat}
    (hm : 0 < m)
    (h : m ≤ featureDeficiencyCandidate f x r) :
    BitString.blen f + BitString.blen r < BitString.blen x ∧
      runs f r x ∧
      m ≤ BitString.blen x - BitString.blen r - 1 := by
  classical
  by_cases hlt : BitString.blen f + BitString.blen r < BitString.blen x
  · by_cases hrun : runs f r x
    · simp [featureDeficiencyCandidate, hlt, hrun] at h
      exact ⟨hlt, hrun, h⟩
    · have hm0 : m = 0 := by simpa [featureDeficiencyCandidate, hlt, hrun] using h
      omega
  · have hm0 : m = 0 := by simpa [featureDeficiencyCandidate, hlt] using h
    omega

theorem exists_residual_of_featureRandomnessTest_ge {f x : Program} {m : Nat}
    (hm : 0 < m)
    (h : m ≤ featureRandomnessTest f x) :
    ∃ r ∈ BitString.allUpToLength (BitString.blen x),
      BitString.blen f + BitString.blen r < BitString.blen x ∧
      runs f r x ∧
      m ≤ BitString.blen x - BitString.blen r - 1 := by
  unfold featureRandomnessTest at h
  rcases exists_mem_of_foldl_max_ge hm h with ⟨d, hdmem, hdm⟩
  rcases List.mem_map.1 hdmem with ⟨r, hrmem, rfl⟩
  exact ⟨r, hrmem, featureDeficiencyCandidate_ge hm hdm⟩

theorem featureRandomness_levelBound (f : Program) :
    ∀ n m, (randomnessLevelSet (featureRandomnessTest f) n m).length ≤ 2 ^ (n - m)
  | n, 0 => by
      unfold randomnessLevelSet
      calc
        ((BitString.allOfLength n).filter fun x => decide (0 ≤ featureRandomnessTest f x)).length ≤
            (BitString.allOfLength n).length := by
          exact List.length_filter_le _ _
        _ = 2 ^ n := BitString.length_allOfLength n
        _ = 2 ^ (n - 0) := by simp
  | n, m + 1 => by
      let S := randomnessLevelSet (featureRandomnessTest f) n (m + 1)
      let A := (BitString.allUpToLength (n - (m + 1) - 1)).toFinset
      have hSNodup : S.Nodup := nodup_randomnessLevelSet _ _ _
      have hANodup : (BitString.allUpToLength (n - (m + 1) - 1)).Nodup :=
        BitString.nodup_allUpToLength _
      have hmemS {x : Program} (hx : x ∈ S) :
          BitString.blen x = n ∧ m + 1 ≤ featureRandomnessTest f x := by
        have hx' : x ∈ randomnessLevelSet (featureRandomnessTest f) n (m + 1) := by
          simpa [S] using hx
        simpa using (mem_randomnessLevelSet_iff.mp hx')
      have himage :
          S.toFinset.card ≤ A.card := by
        classical
        let w : S.toFinset → A := fun x => by
          let hxS : x.1 ∈ S := List.mem_toFinset.mp x.2
          let hwit :=
            exists_residual_of_featureRandomnessTest_ge
              (f := f) (x := x.1) (m := m + 1) (Nat.succ_pos _)
              (hmemS hxS).2
          let r := Classical.choose hwit
          have hrLe : BitString.blen r ≤ n - (m + 1) - 1 := by
            rcases Classical.choose_spec hwit with ⟨hrmem, hlt, hrun, hmle⟩
            have hmle' : m + 1 ≤ n - BitString.blen r - 1 := by
              simpa [r, (hmemS hxS).1] using hmle
            omega
          have hrA : r ∈ A := by
            change r ∈ (BitString.allUpToLength (n - (m + 1) - 1)).toFinset
            exact List.mem_toFinset.mpr (BitString.mem_allUpToLength_iff.mpr hrLe)
          exact ⟨r, hrA⟩
        have hw_inj : Function.Injective w := by
          intro x y hxy
          apply Subtype.ext
          have hxS : x.1 ∈ S := List.mem_toFinset.mp x.2
          have hyS : y.1 ∈ S := List.mem_toFinset.mp y.2
          let hxwit :=
            exists_residual_of_featureRandomnessTest_ge
              (f := f) (x := x.1) (m := m + 1) (Nat.succ_pos _)
              (hmemS hxS).2
          let hywit :=
            exists_residual_of_featureRandomnessTest_ge
              (f := f) (x := y.1) (m := m + 1) (Nat.succ_pos _)
              (hmemS hyS).2
          have hrunx : runs f (Classical.choose hxwit) x.1 := by
            rcases Classical.choose_spec hxwit with ⟨hrmem, hlt, hrun, hmle⟩
            exact hrun
          have hruny : runs f (Classical.choose hywit) y.1 := by
            rcases Classical.choose_spec hywit with ⟨hrmem, hlt, hrun, hmle⟩
            exact hrun
          have hwEq : (w x : Program) = (w y : Program) := congrArg Subtype.val hxy
          have hrunx' : runs f (w x) x.1 := by
            simpa [w, hxwit] using hrunx
          have hruny' : runs f (w y) y.1 := by
            simpa [w, hywit] using hruny
          have hruny'' : runs f (w x) y.1 := by
            rw [← hwEq] at hruny'
            exact hruny'
          exact runs_deterministic hrunx' hruny''
        simpa [A] using Finset.card_le_card_of_injective (f := w) hw_inj
      calc
        S.length = S.toFinset.card := by
          simpa [S] using (List.toFinset_card_of_nodup hSNodup).symm
        _ ≤ A.card := himage
        _ = (BitString.allUpToLength (n - (m + 1) - 1)).length := by
          simpa [A] using List.toFinset_card_of_nodup hANodup
        _ ≤ 2 ^ (n - (m + 1)) := by
          rw [BitString.length_allUpToLength]
          let k := n - (m + 1)
          by_cases hk : k = 0
          · simp [k, hk]
          · have hkpos : 0 < k := Nat.pos_iff_ne_zero.mpr hk
            have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
            rw [hk1]
            exact Nat.sub_le _ _

theorem featureRandomnessTest_isUniformMartinLofTest (f : Program) :
    IsUniformMartinLofTest (featureRandomnessTest f) := by
  refine ⟨featureRandomnessTest_lowerSemicomputable f, ?_⟩
  intro n m
  exact featureRandomness_levelBound f n m

/-- Paper-facing Theorem 5.1. The assumption that `f` is a feature somewhere is stronger than
what the current formalization actually needs, but keeps the statement aligned with the paper. -/
theorem theorem51 {f : Program}
    (hf : ∃ x, IsFeature runs f x) :
    IsUniformMartinLofTest (featureRandomnessTest f) := by
  exact featureRandomnessTest_isUniformMartinLofTest f

end

end Compression

end IcTheory
