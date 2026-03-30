import IcTheory.Compression.Theorem51
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

/-- Project-style unboundedness for a randomness test. This matches the paper's qualitative
assumption and is the unboundedness hypothesis used in the paper-form Theorem 5.2 below. -/
def IsUnboundedMartinLofTest (δ : Program → Nat) : Prop :=
  ∀ c : Nat, ∃ x : Program, c < δ x

/-- Decode an index `i < 2^n` as a bitstring of exactly length `n`. This is the paper's padded
index encoding for residuals of length `n - m`. -/
def ofNatFixed : Nat → Nat → Program
  | 0, _ => []
  | n + 1, i =>
      let p := 2 ^ n
      if i < p then false :: ofNatFixed n i else true :: ofNatFixed n (i - p)

@[simp] theorem blen_ofNatFixed (n i : Nat) :
    BitString.blen (ofNatFixed n i) = n := by
  induction n generalizing i with
  | zero =>
      simp [ofNatFixed]
  | succ n ih =>
      by_cases h : i < 2 ^ n
      · simp [ofNatFixed, h, ih]
      · simp [ofNatFixed, h, ih]

theorem getElem?_allOfLength_ofNatFixed {n i : Nat} (hi : i < 2 ^ n) :
    (BitString.allOfLength n)[i]? = some (ofNatFixed n i) := by
  induction n generalizing i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst hi0
      simp [BitString.allOfLength, ofNatFixed]
  | succ n ih =>
      let p := 2 ^ n
      by_cases hip : i < p
      · have hip0 : i < 2 ^ n := by
          simpa [p] using hip
        rw [BitString.allOfLength, List.getElem?_append_left]
        · rw [List.getElem?_map]
          simpa [ofNatFixed, hip, p] using
            congrArg (Option.map (List.cons false)) (ih hip0)
        · simpa [BitString.length_allOfLength] using hip
      · have hip' : p ≤ i := Nat.le_of_not_gt hip
        have hi' : i - p < 2 ^ n := by
          dsimp [p] at hi ⊢
          omega
        rw [BitString.allOfLength, List.getElem?_append_right]
        · rw [List.getElem?_map]
          simpa [BitString.length_allOfLength, ofNatFixed, hip, p] using
            congrArg (Option.map (List.cons true)) (ih hi')
        · simpa [BitString.length_allOfLength, p] using hip'

theorem idxOf_allOfLength_ofNatFixed {n i : Nat} (hi : i < 2 ^ n) :
    (BitString.allOfLength n).idxOf (ofNatFixed n i) = i := by
  have hlen : i < (BitString.allOfLength n).length := by
    simpa using hi
  have hget :
      (BitString.allOfLength n)[i] = ofNatFixed n i := by
    have := getElem?_allOfLength_ofNatFixed hi
    have : some ((BitString.allOfLength n)[i]) = some (ofNatFixed n i) := by
      simpa [List.getElem?_eq_getElem hlen] using this
    exact Option.some.inj this
  rw [← hget]
  exact (BitString.nodup_allOfLength n).idxOf_getElem i hlen

private theorem listBEq_eq_instBEqOfDecidableEq [DecidableEq α] :
    List.instBEq = @instBEqOfDecidableEq (List α) instDecidableEqList := by
  exact congrArg BEq.mk <| by
    funext l₁ l₂
    change (l₁ == l₂) = _
    rw [Bool.eq_iff_iff, @beq_iff_eq _ (_), decide_eq_true_iff]

/-- Recover the lexicographic index of a fixed-length residual inside `allOfLength`. -/
def fixedLengthIndex (r : Program) : Nat :=
  List.idxOf r (BitString.allOfLength (List.length r))

@[simp] theorem fixedLengthIndex_ofNatFixed {n i : Nat} (hi : i < 2 ^ n) :
    fixedLengthIndex (ofNatFixed n i) = i := by
  simpa [fixedLengthIndex] using (idxOf_allOfLength_ofNatFixed hi)

/-- Abstract fixed decoder for the `m`-th randomness-test level set. For every `x` of length `n`
with `δ(x) ≥ m`, the decoder reconstructs `x` from some padded index of length `n - m`. The rest
of this file constructs such a decoder uniformly from a uniform unbounded Martin-Lof test. -/
def IsRandomnessLevelIndexDecoder (δ : Program → Nat) (m : Nat) (f : Program) : Prop :=
  ∀ n : Nat, ∀ x : Program,
    x ∈ randomnessLevelSet δ n m →
      ∃ i < 2 ^ (n - m), runs f (ofNatFixed (n - m) i) x

/-- If a fixed decoder reconstructs every string in the `m`-th level set from a residual of length
`n - m`, and the decoder itself is shorter than `m`, then it is a feature of every string in that
level set. The strengthened notion of uniform test guarantees that strings with `δ(x) ≥ m` do
indeed have length at least `m`. -/
theorem randomnessLevelIndexDecoder_isFeature_of_lengthGap {δ : Program → Nat}
    {m : Nat} {f x : Program}
    (hδ : IsUniformMartinLofTest δ)
    (hdecoder : IsRandomnessLevelIndexDecoder δ m f)
    (hgap : BitString.blen f < m)
    (hxm : m ≤ δ x) :
    IsFeature runs f x := by
  have hxLevel : x ∈ randomnessLevelSet δ (BitString.blen x) m := by
    exact (mem_randomnessLevelSet_iff).2 ⟨rfl, hxm⟩
  have hmxLen : m ≤ BitString.blen x := by
    by_contra hlt
    have hxempty : randomnessLevelSet δ (BitString.blen x) m = [] :=
      hδ.empty_of_length_lt (Nat.lt_of_not_ge hlt)
    simpa [hxempty] using hxLevel
  obtain ⟨i, hi, hrun⟩ := hdecoder (BitString.blen x) x hxLevel
  let r := ofNatFixed (BitString.blen x - m) i
  have hrLen : BitString.blen r = BitString.blen x - m := by
    simp [r, blen_ofNatFixed]
  refine ⟨codeToProgram (Code.const (BitString.toNatExact r)), ?_⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · exact (runs_const_iff (BitString.toNatExact r) x r).2
      (BitString.ofNatExact_toNatExact r).symm
  · simpa [r] using hrun
  · unfold CompressionCondition
    rw [hrLen]
    omega

/-- Concrete plain program computing the stage approximation `φ(t, x)`. -/
def IsRandomnessApproximationProgram (φ : Nat → Program → Nat) (p : Program) : Prop :=
  ∀ t x, runs p (packedInput (BitString.ofNatExact t) x) (BitString.ofNatExact (φ t x))

theorem exists_randomnessApproximationProgram {φ : Nat → Program → Nat}
    (hφ : Computable fun a : Nat × Program => φ a.1 a.2) :
    ∃ p : Program, IsRandomnessApproximationProgram φ p := by
  let φNat : Nat → Nat := fun inputNat =>
    φ inputNat.unpair.1 (BitString.ofNatExact inputNat.unpair.2)
  have hφNat : Computable φNat := by
    exact hφ.comp
      (Computable.pair
        (Computable.fst.comp Computable.unpair)
        (BitString.ofNatExact_computable.comp (Computable.snd.comp Computable.unpair)))
  obtain ⟨c, hc⟩ := Code.exists_code.1 hφNat.partrec
  refine ⟨codeToProgram c, ?_⟩
  intro t x
  rw [runs_codeToProgram_iff, hc]
  simp [φNat, toNatExact_packedInput]

/-- The theorem 5.2 feature stores the approximation program, the chosen threshold `m`, and an
optional padding tail. The new plain stored-payload wrapper makes the feature length linear in that
padding, so the paper's `|f| = m - 1` normalization can be realized exactly. -/
def randomnessLevelPayload (approx : Program) (m : Nat) (pad : Program) : Program :=
  BitString.exactPairPayload approx (BitString.exactPairPayload (BitString.ofNatExact m) pad)

def decodeRandomnessLevelPayload (payload : Program) : Program × Nat × Program :=
  let outer := BitString.decodeExactPairPayload payload
  let inner := BitString.decodeExactPairPayload outer.2
  (outer.1, BitString.toNatExact inner.1, inner.2)

@[simp] theorem decodeRandomnessLevelPayload_payload (approx : Program) (m : Nat) (pad : Program) :
    decodeRandomnessLevelPayload (randomnessLevelPayload approx m pad) = (approx, m, pad) := by
  simp [decodeRandomnessLevelPayload, randomnessLevelPayload]

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

private theorem allOfLength_computable : Computable BitString.allOfLength :=
  allOfLength_primrec.to_comp

private theorem fixedLengthIndex_computable : Computable fixedLengthIndex := by
  convert
    ((Primrec.list_idxOf.to_comp).comp
      Computable.id
      (allOfLength_computable.comp Primrec.list_length.to_comp)) using 1
  funext r
  simp [fixedLengthIndex, listBEq_eq_instBEqOfDecidableEq]

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
      (programToCode_primrec.comp (Primrec.fst.comp Primrec.snd))
  exact (Primrec.option_map hEvaln
    ((BitString.ofNatExact_primrec.comp Primrec.snd).to₂)).of_eq fun a => by
      cases a with
      | mk k rest =>
          cases rest with
          | mk p input =>
              rfl

private theorem appendIfNew_primrec : Primrec₂ appendIfNew := by
  have hmem : PrimrecRel fun (xs : List Program) (y : Program) => y ∈ xs := by
    simpa using
      (PrimrecRel.exists_mem_list
        (R := fun a b : Program => a = b)
        (hf := (Primrec.eq : PrimrecRel (fun a b : Program => a = b))))
  have hsome :
      Primrec₂ fun (a : List Program × Option Program) (y : Program) =>
        if y ∈ a.1 then a.1 else a.1 ++ [y] := by
    exact (Primrec.ite
      (show PrimrecPred fun p : (List Program × Option Program) × Program =>
        p.2 ∈ p.1.1 from
          PrimrecRel.comp hmem (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
      (Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  refine (Primrec.option_casesOn
    (ho := Primrec.snd)
    (hf := Primrec.fst)
    (hg := hsome)).to₂.of_eq ?_
  intro xs oy
  cases oy with
  | none =>
      rfl
  | some y =>
      by_cases hy : y ∈ xs <;> simp [appendIfNew, hy]

private theorem appendIfNew_computable : Computable₂ appendIfNew :=
  appendIfNew_primrec.to_comp

private theorem getElem?_appendIfNew_of_getElem? {xs : List Program} {oy : Option Program}
    {i : Nat} {y : Program} (hy : xs[i]? = some y) :
    (appendIfNew xs oy)[i]? = some y := by
  have hi : i < xs.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hy
    simp at hy
  cases oy with
  | none =>
      simpa [appendIfNew] using hy
  | some z =>
      by_cases hz : z ∈ xs
      · simpa [appendIfNew, hz] using hy
      · rw [appendIfNew, if_neg hz, List.getElem?_append_left]
        · exact hy
        · exact hi

/-- Decode a search stage into approximation stage, evaluator fuel, and candidate index. -/
def randomnessLevelStageData (q : Nat) : Nat × Nat × Nat :=
  (q.unpair.1, q.unpair.2.unpair.1, q.unpair.2.unpair.2)

@[simp] theorem randomnessLevelStageData_pair (t k j : Nat) :
    randomnessLevelStageData (Nat.pair t (Nat.pair k j)) = (t, k, j) := by
  simp [randomnessLevelStageData]

private theorem randomnessLevelStageData_primrec : Primrec randomnessLevelStageData := by
  unfold randomnessLevelStageData
  exact Primrec.pair
    (Primrec.fst.comp Primrec.unpair)
    (Primrec.pair
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))

private theorem randomnessLevelStageData_computable : Computable randomnessLevelStageData := by
  unfold randomnessLevelStageData
  exact Computable.pair
    (Computable.fst.comp Computable.unpair)
    (Computable.pair
      (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))
      (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))))

private abbrev RandomnessLevelArgs := Program × Nat × Nat × Nat

private def randomnessLevelLookup (a : RandomnessLevelArgs) : Option Program :=
  let data := randomnessLevelStageData a.2.2.2
  (BitString.allOfLength a.2.2.1)[data.2.2]?

private def randomnessLevelRunAtCandidate (a : RandomnessLevelArgs) (x : Program) : Option Program :=
  let data := randomnessLevelStageData a.2.2.2
  (prefixOutputAtFuel data.2.1 a.1 (packedInput (BitString.ofNatExact data.1) x)).bind
    fun out => if a.2.1 ≤ BitString.toNatExact out then some x else none

private theorem randomnessLevelLookup_primrec :
    Primrec fun a : RandomnessLevelArgs => randomnessLevelLookup a := by
  have hstage :
      Primrec fun a : RandomnessLevelArgs => randomnessLevelStageData a.2.2.2 :=
    randomnessLevelStageData_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_getElem?.comp
    (allOfLength_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp hstage))).of_eq fun a => by
      simp [randomnessLevelLookup]

private theorem randomnessLevelLookup_computable : Computable randomnessLevelLookup :=
  randomnessLevelLookup_primrec.to_comp

private theorem randomnessLevelRunAtCandidate_primrec :
    Primrec fun p : RandomnessLevelArgs × Program => randomnessLevelRunAtCandidate p.1 p.2 := by
  have hstage :
      Primrec fun p : RandomnessLevelArgs × Program =>
        randomnessLevelStageData p.1.2.2.2 :=
    randomnessLevelStageData_primrec.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hrunArg :
      Primrec fun p : RandomnessLevelArgs × Program =>
        ((randomnessLevelStageData p.1.2.2.2).2.1,
          p.1.1,
          packedInput (BitString.ofNatExact (randomnessLevelStageData p.1.2.2.2).1) p.2) := by
    refine Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hstage)) ?_
    refine Primrec.pair (Primrec.fst.comp Primrec.fst) ?_
    exact packedInput_primrec.comp
      (BitString.ofNatExact_primrec.comp (Primrec.fst.comp hstage))
      Primrec.snd
  have hrun :
      Primrec fun p : RandomnessLevelArgs × Program =>
        prefixOutputAtFuel (randomnessLevelStageData p.1.2.2.2).2.1
          p.1.1 (packedInput (BitString.ofNatExact (randomnessLevelStageData p.1.2.2.2).1) p.2) :=
    prefixOutputAtFuel_primrec.comp hrunArg
  have hpred :
      PrimrecPred fun p : (RandomnessLevelArgs × Program) × Program =>
        p.1.1.2.1 ≤ BitString.toNatExact p.2 := by
    exact PrimrecRel.comp Primrec.nat_le
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (BitString.toNatExact_primrec.comp Primrec.snd)
  have hsome :
      Primrec fun p : (RandomnessLevelArgs × Program) × Program =>
        some p.1.2 :=
    Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)
  have hselect :
      Primrec₂ fun (p : RandomnessLevelArgs × Program) (out : Program) =>
        if p.1.2.1 ≤ BitString.toNatExact out then some p.2 else none := by
    exact (Primrec.ite hpred hsome (Primrec.const (Option.none : Option Program))).to₂
  exact (Primrec.option_bind hrun hselect).of_eq fun p => by
    cases p with
    | mk a x =>
        simp [randomnessLevelRunAtCandidate]

/-- A single discovery attempt for the finite level set `V_m^n`, driven by the computable
approximation program. -/
noncomputable def randomnessLevelCandidateAtStep (approx : Program) (m n q : Nat) :
    Option Program :=
  (randomnessLevelLookup (approx, m, n, q)).bind
    (randomnessLevelRunAtCandidate (approx, m, n, q))

private theorem randomnessLevelCandidateAtStep_primrec :
    Primrec fun a : Program × Nat × Nat × Nat =>
      randomnessLevelCandidateAtStep a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  exact (Primrec.option_bind randomnessLevelLookup_primrec
    randomnessLevelRunAtCandidate_primrec.to₂).of_eq fun a => by
      cases a with
      | mk approx mnq =>
          cases mnq with
          | mk m nq =>
              cases nq with
              | mk n q =>
                  simp [randomnessLevelCandidateAtStep]

private theorem randomnessLevelCandidateAtStep_computable :
    Computable fun a : Program × Nat × Nat × Nat =>
      randomnessLevelCandidateAtStep a.1 a.2.1 a.2.2.1 a.2.2.2 :=
  randomnessLevelCandidateAtStep_primrec.to_comp

/-- Finite discovery list for the recursively enumerable level set `V_m^n`. -/
noncomputable def randomnessLevelDiscoveredUpToStep (approx : Program) (m n : Nat) : Nat → List Program
  | 0 => []
  | q + 1 =>
      appendIfNew (randomnessLevelDiscoveredUpToStep approx m n q)
        (randomnessLevelCandidateAtStep approx m n q)

@[simp] theorem randomnessLevelDiscoveredUpToStep_zero (approx : Program) (m n : Nat) :
    randomnessLevelDiscoveredUpToStep approx m n 0 = [] := rfl

@[simp] theorem randomnessLevelDiscoveredUpToStep_succ (approx : Program) (m n q : Nat) :
    randomnessLevelDiscoveredUpToStep approx m n (q + 1) =
      appendIfNew (randomnessLevelDiscoveredUpToStep approx m n q)
        (randomnessLevelCandidateAtStep approx m n q) := rfl

private theorem approximation_le_of_lowerSemicomputable
    {δ : Program → Nat} {φ : Nat → Program → Nat}
    (hmono : ∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x)
    (t : Nat) (x : Program) :
    φ t x ≤ δ x := by
  rcases hlim x with ⟨T, hT⟩
  have htx : φ t x ≤ φ (max t T) x := hmono (Nat.le_max_left _ _) 
  rw [hT (Nat.le_max_right _ _)] at htx
  exact htx

private theorem randomnessLevelCandidateAtStep_sound
    {δ : Program → Nat} {φ : Nat → Program → Nat} {approx x : Program}
    {m n q : Nat}
    (happrox : IsRandomnessApproximationProgram φ approx)
    (hmono : ∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x)
    (hx : randomnessLevelCandidateAtStep approx m n q = some x) :
    x ∈ randomnessLevelSet δ n m := by
  unfold randomnessLevelCandidateAtStep at hx
  rw [Option.bind_eq_some_iff] at hx
  rcases hx with ⟨candidate, hlookup, hrun⟩
  have hmem : candidate ∈ BitString.allOfLength n := by
    rw [List.mem_iff_getElem?]
    refine ⟨(randomnessLevelStageData q).2.2, ?_⟩
    simpa [randomnessLevelLookup] using hlookup
  have hlen : BitString.blen candidate = n := BitString.mem_allOfLength_iff.mp hmem
  unfold randomnessLevelRunAtCandidate at hrun
  rw [Option.bind_eq_some_iff] at hrun
  rcases hrun with ⟨out, hout, houtEq⟩
  by_cases hm : m ≤ BitString.toNatExact out
  · simp [hm] at houtEq
    subst x
    have hrunApprox :
        runs approx
          (packedInput (BitString.ofNatExact (randomnessLevelStageData q).1) candidate) out :=
      prefixOutputAtFuel_sound hout
    have houtVal :
        out = BitString.ofNatExact (φ (randomnessLevelStageData q).1 candidate) :=
      runs_deterministic hrunApprox (happrox _ _)
    have hmφ : m ≤ φ (randomnessLevelStageData q).1 candidate := by
      simpa [houtVal] using hm
    refine (mem_randomnessLevelSet_iff).2 ⟨hlen, ?_⟩
    exact le_trans hmφ
      (approximation_le_of_lowerSemicomputable
        (δ := δ) (φ := φ) hmono hlim (randomnessLevelStageData q).1 candidate)
  · simp [hm] at houtEq

private theorem randomnessLevelCandidateAtStep_complete
    {δ : Program → Nat} {φ : Nat → Program → Nat} {approx x : Program}
    {m n : Nat}
    (happrox : IsRandomnessApproximationProgram φ approx)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x)
    (hx : x ∈ randomnessLevelSet δ n m) :
    ∃ q, randomnessLevelCandidateAtStep approx m n q = some x := by
  rcases (mem_randomnessLevelSet_iff).1 hx with ⟨hxn, hxm⟩
  have hxMem : x ∈ BitString.allOfLength n := (BitString.mem_allOfLength_iff).2 hxn
  rw [List.mem_iff_getElem?] at hxMem
  rcases hxMem with ⟨j, hj⟩
  rcases hlim x with ⟨t, ht⟩
  have htEq : φ t x = δ x := ht le_rfl
  rcases prefixOutputAtFuel_complete (happrox t x) with ⟨k, hk⟩
  refine ⟨Nat.pair t (Nat.pair k j), ?_⟩
  simp [randomnessLevelCandidateAtStep, randomnessLevelLookup, randomnessLevelRunAtCandidate,
    randomnessLevelStageData_pair, hj, hk, htEq, hxm]

private theorem nodup_randomnessLevelDiscoveredUpToStep (approx : Program) (m n q : Nat) :
    (randomnessLevelDiscoveredUpToStep approx m n q).Nodup := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      simpa [randomnessLevelDiscoveredUpToStep_succ] using
        nodup_appendIfNew ih (randomnessLevelCandidateAtStep approx m n q)

private theorem mem_randomnessLevelDiscoveredUpToStep_sound
    {δ : Program → Nat} {φ : Nat → Program → Nat} {approx x : Program}
    {m n q : Nat}
    (happrox : IsRandomnessApproximationProgram φ approx)
    (hmono : ∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x)
    (hx : x ∈ randomnessLevelDiscoveredUpToStep approx m n q) :
    x ∈ randomnessLevelSet δ n m := by
  induction q with
  | zero =>
      simpa [randomnessLevelDiscoveredUpToStep] using hx
  | succ q ih =>
      rw [randomnessLevelDiscoveredUpToStep_succ, mem_appendIfNew_iff] at hx
      rcases hx with hx | hx
      · exact ih hx
      · exact randomnessLevelCandidateAtStep_sound happrox hmono hlim hx

private theorem randomnessLevelDiscoveredUpToStep_getElem?_mono
    {approx : Program} {m n q r i : Nat} {x : Program}
    (hqr : q ≤ r)
    (hx : (randomnessLevelDiscoveredUpToStep approx m n q)[i]? = some x) :
    (randomnessLevelDiscoveredUpToStep approx m n r)[i]? = some x := by
  induction hqr with
  | refl =>
      exact hx
  | @step r hqr ih =>
      rw [randomnessLevelDiscoveredUpToStep_succ]
      exact getElem?_appendIfNew_of_getElem? ih

private theorem randomnessLevelDiscoveredUpToStep_length_le
    {δ : Program → Nat} {φ : Nat → Program → Nat} {approx : Program}
    {m n q : Nat}
    (hδ : IsUniformMartinLofTest δ)
    (happrox : IsRandomnessApproximationProgram φ approx)
    (hmono : ∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x) :
    (randomnessLevelDiscoveredUpToStep approx m n q).length ≤ 2 ^ (n - m) := by
  let s : Finset Program :=
    ⟨randomnessLevelDiscoveredUpToStep approx m n q,
      nodup_randomnessLevelDiscoveredUpToStep approx m n q⟩
  let t : Finset Program :=
    ⟨randomnessLevelSet δ n m, nodup_randomnessLevelSet δ n m⟩
  have hsubset : s ⊆ t := by
    intro x hx
    exact mem_randomnessLevelDiscoveredUpToStep_sound happrox hmono hlim hx
  have hcard := Finset.card_le_card hsubset
  simpa [s, t] using le_trans hcard (hδ.levelBound n m)

private theorem decodeRandomnessLevelPayload_computable :
    Computable decodeRandomnessLevelPayload := by
  unfold decodeRandomnessLevelPayload
  have houter : Computable fun payload : Program => BitString.decodeExactPairPayload payload :=
    BitString.decodeExactPairPayload_computable
  have hinner :
      Computable fun payload : Program =>
        BitString.decodeExactPairPayload (BitString.decodeExactPairPayload payload).2 := by
    exact BitString.decodeExactPairPayload_computable.comp (Computable.snd.comp houter)
  exact Computable.pair
    (Computable.fst.comp houter)
    (Computable.pair
      (BitString.toNatExact_computable.comp (Computable.fst.comp hinner))
      (Computable.snd.comp hinner))

private theorem unpackInput_computable : Computable unpackInput := by
  refine (Computable.pair
      (BitString.ofNatExact_computable.comp
        (Computable.fst.comp (Computable.unpair.comp BitString.toNatExact_computable)))
      (BitString.ofNatExact_computable.comp
        (Computable.snd.comp (Computable.unpair.comp BitString.toNatExact_computable)))).of_eq ?_
  intro z
  rfl

private theorem randomnessLevelDiscoveredUpToStep_primrec :
    Primrec fun a : Program × Nat × Nat × Nat =>
      randomnessLevelDiscoveredUpToStep a.1 a.2.1 a.2.2.1 a.2.2.2 := by
  have hcandArg :
      Primrec fun p : (Program × Nat × Nat × Nat) × (Nat × List Program) =>
        (p.1.1, p.1.2.1, p.1.2.2.1, p.2.1) := by
    exact Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.fst.comp Primrec.snd)))
  have hstep :
      Primrec₂ fun (a : Program × Nat × Nat × Nat) (p : Nat × List Program) =>
        appendIfNew p.2 (randomnessLevelCandidateAtStep a.1 a.2.1 a.2.2.1 p.1) := by
    exact appendIfNew_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (randomnessLevelCandidateAtStep_primrec.comp hcandArg)
  refine (Primrec.nat_rec' (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.const ([] : List Program)) hstep).of_eq ?_
  intro a
  cases a with
  | mk approx mnq =>
      cases mnq with
      | mk m nq =>
          cases nq with
          | mk n q =>
              induction q with
              | zero =>
                  rfl
              | succ q ih =>
                  simp [randomnessLevelDiscoveredUpToStep, ih]

private theorem randomnessLevelDiscoveredUpToStep_computable :
    Computable fun a : Program × Nat × Nat × Nat =>
      randomnessLevelDiscoveredUpToStep a.1 a.2.1 a.2.2.1 a.2.2.2 :=
  randomnessLevelDiscoveredUpToStep_primrec.to_comp

/-- The stabilized `i`-th element of the discovered level-set list. -/
private noncomputable def randomnessLevelSearchStep
    (approx : Program) (m n i : Nat) (q : Nat) : Option Program :=
  (randomnessLevelDiscoveredUpToStep approx m n q)[i]?

private theorem randomnessLevelSearchStep_primrec :
    Primrec₂ fun (a : Program × Nat × Nat × Nat) (q : Nat) =>
      randomnessLevelSearchStep a.1 a.2.1 a.2.2.1 a.2.2.2 q := by
  simpa [randomnessLevelSearchStep] using
    (Primrec.list_getElem?.comp
      (randomnessLevelDiscoveredUpToStep_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.pair
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
              Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))

private theorem randomnessLevelSearchStep_computable :
    Computable₂ fun (a : Program × Nat × Nat × Nat) (q : Nat) =>
      randomnessLevelSearchStep a.1 a.2.1 a.2.2.1 a.2.2.2 q :=
  randomnessLevelSearchStep_primrec.to_comp

private def randomnessLevelArgsOfNat (inputNat : Nat) : Program × Nat × Nat × Nat :=
  let rp := unpackInput (BitString.ofNatExact inputNat)
  let decoded := decodeRandomnessLevelPayload rp.2
  (decoded.1, decoded.2.1, BitString.blen rp.1 + decoded.2.1, fixedLengthIndex rp.1)

@[simp] private theorem randomnessLevelArgsOfNat_packedInput
    (r approx pad : Program) (m : Nat) :
    randomnessLevelArgsOfNat
        (BitString.toNatExact (packedInput r (randomnessLevelPayload approx m pad))) =
      (approx, m, BitString.blen r + m, fixedLengthIndex r) := by
  rw [randomnessLevelArgsOfNat, BitString.ofNatExact_toNatExact, unpackInput_packedInput,
    decodeRandomnessLevelPayload_payload]

private theorem randomnessLevelArgsOfNat_computable :
    Computable randomnessLevelArgsOfNat := by
  have hrp :
      Computable fun inputNat : Nat => unpackInput (BitString.ofNatExact inputNat) := by
    exact unpackInput_computable.comp BitString.ofNatExact_computable
  have hdecoded :
      Computable fun inputNat : Nat =>
        decodeRandomnessLevelPayload (unpackInput (BitString.ofNatExact inputNat)).2 := by
    exact decodeRandomnessLevelPayload_computable.comp (Computable.snd.comp hrp)
  exact Computable.pair
    (Computable.fst.comp hdecoded)
    (Computable.pair
      (Computable.fst.comp (Computable.snd.comp hdecoded))
      (Computable.pair
        ((Primrec.nat_add.to_comp).comp
          (Primrec.list_length.to_comp.comp (Computable.fst.comp hrp))
          (Computable.fst.comp (Computable.snd.comp hdecoded)))
        (fixedLengthIndex_computable.comp (Computable.fst.comp hrp))))

private noncomputable def randomnessLevelSearchStepNat (inputNat q : Nat) : Option Nat :=
  let a := randomnessLevelArgsOfNat inputNat
  (randomnessLevelSearchStep a.1 a.2.1 a.2.2.1 a.2.2.2 q).map BitString.toNatExact

@[simp] private theorem randomnessLevelSearchStepNat_packedInput
    (r approx pad : Program) (m q : Nat) :
    randomnessLevelSearchStepNat
        (BitString.toNatExact (packedInput r (randomnessLevelPayload approx m pad))) q =
      (randomnessLevelSearchStep approx m (BitString.blen r + m) (fixedLengthIndex r) q).map
        BitString.toNatExact := by
  rw [randomnessLevelSearchStepNat, randomnessLevelArgsOfNat_packedInput]

private theorem randomnessLevelSearchStepNat_computable :
    Computable₂ randomnessLevelSearchStepNat := by
  exact Computable.option_map
    (randomnessLevelSearchStep_computable.comp
      (randomnessLevelArgsOfNat_computable.comp Computable.fst)
      Computable.snd)
    ((BitString.toNatExact_computable.comp Computable.snd).to₂)

private theorem randomnessLevelSearcherNat_partrec :
    Nat.Partrec fun inputNat => Nat.rfindOpt (randomnessLevelSearchStepNat inputNat) := by
  exact Partrec.nat_iff.1 (Partrec.rfindOpt randomnessLevelSearchStepNat_computable)

private theorem exists_randomnessLevelSearcherCode :
    ∃ c : Nat.Partrec.Code,
      ∀ inputNat : Nat,
        Nat.Partrec.Code.eval c inputNat = Nat.rfindOpt (randomnessLevelSearchStepNat inputNat) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 randomnessLevelSearcherNat_partrec
  exact ⟨c, fun inputNat => by simpa using congrFun hc inputNat⟩

/-- Fixed plain decoder used in the formalization of Theorem 5.2. It takes the packed pair
`⟨r, payload⟩`, recovers `(approx, m)` from `payload`, and searches for the corresponding
level-set element indexed by `r`. -/
noncomputable def randomnessLevelSearcher : Program :=
  UniversalMachine.codeToProgram (Classical.choose exists_randomnessLevelSearcherCode)

private theorem eval_randomnessLevelSearcherCode (inputNat : Nat) :
    Nat.Partrec.Code.eval (Classical.choose exists_randomnessLevelSearcherCode) inputNat =
      Nat.rfindOpt (randomnessLevelSearchStepNat inputNat) :=
  Classical.choose_spec exists_randomnessLevelSearcherCode inputNat

/-- The fixed amount of plain-program overhead contributed by the theorem 5.2 decoder wrapper,
excluding the stored payload and residual. -/
noncomputable def randomnessLevelFeaturePlainOverhead : Nat :=
  BitString.blen randomnessLevelSearcher +
    (2 * BitString.blen (BitString.ofNatExact (BitString.blen randomnessLevelSearcher)) + 9)

/-- The actual feature program produced from the approximation witness and the chosen threshold. -/
noncomputable def randomnessLevelFeature (approx : Program) (m : Nat) (pad : Program) : Program :=
  postcomposePackedProgram randomnessLevelSearcher
    (packInputWithPayloadPackedProgram (randomnessLevelPayload approx m pad))

@[simp] theorem blen_randomnessLevelFeature (approx : Program) (m : Nat) (pad : Program) :
    BitString.blen (randomnessLevelFeature approx m pad) =
      BitString.blen pad + BitString.blen approx + BitString.blen (BitString.ofNatExact m) +
        2 * BitString.blen (BitString.ofNatExact (BitString.blen approx)) +
        2 * BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact m))) +
        randomnessLevelFeaturePlainOverhead + 2 := by
  simp [randomnessLevelFeature, randomnessLevelPayload, randomnessLevelFeaturePlainOverhead,
    BitString.blen_exactPairPayload, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

private theorem randomnessLevelFeature_runs_of_searcher
    {approx payloadInput : Program} {m : Nat} {pad x : Program}
    (hsearch :
      runs randomnessLevelSearcher
        (packedInput payloadInput (randomnessLevelPayload approx m pad)) x) :
    runs (randomnessLevelFeature approx m pad) payloadInput x := by
  refine runs_postcomposePackedProgram_of_runs ?_ hsearch
  simpa [randomnessLevelFeature, packedInput, randomnessLevelPayload] using
    (runs_packInputWithPayloadPackedProgram_iff
      (payload := randomnessLevelPayload approx m pad)
      (input := payloadInput)
      (output := packedInput payloadInput (randomnessLevelPayload approx m pad))).2 rfl

private theorem randomnessLevelSearcher_runs_of_getElem
    {approx x pad : Program} {m n i q : Nat}
    (hi : i < 2 ^ (n - m))
    (hnm : m ≤ n)
    (hq : (randomnessLevelDiscoveredUpToStep approx m n q)[i]? = some x) :
    runs randomnessLevelSearcher
      (packedInput (ofNatFixed (n - m) i) (randomnessLevelPayload approx m pad)) x := by
  let inputNat := BitString.toNatExact
    (packedInput (ofNatFixed (n - m) i) (randomnessLevelPayload approx m pad))
  have hmono :
      ∀ {a s u}, s ≤ u →
        a ∈ randomnessLevelSearchStepNat inputNat s →
        a ∈ randomnessLevelSearchStepNat inputNat u := by
    intro a s u hsu hs
    rw [randomnessLevelSearchStepNat_packedInput] at hs ⊢
    rw [Option.mem_def] at hs ⊢
    simp [fixedLengthIndex_ofNatFixed hi, blen_ofNatFixed, Nat.sub_add_cancel hnm] at hs ⊢
    rcases hstep : randomnessLevelSearchStep approx m n i s with _ | y
    · simp [hstep] at hs
    · simp [hstep] at hs
      subst a
      have hstep' : randomnessLevelSearchStep approx m n i u = some y := by
        exact randomnessLevelDiscoveredUpToStep_getElem?_mono hsu hstep
      simp [hstep']
  have hstepNat : BitString.toNatExact x ∈ randomnessLevelSearchStepNat inputNat q := by
    rw [randomnessLevelSearchStepNat_packedInput]
    simp [randomnessLevelSearchStep, fixedLengthIndex_ofNatFixed hi, blen_ofNatFixed,
      Nat.sub_add_cancel hnm, hq]
  have hrfind : BitString.toNatExact x ∈ Nat.rfindOpt (randomnessLevelSearchStepNat inputNat) := by
    exact (Nat.rfindOpt_mono hmono).2 ⟨q, hstepNat⟩
  rw [randomnessLevelSearcher, UniversalMachine.runs_codeToProgram_iff]
  change Nat.Partrec.Code.eval (Classical.choose exists_randomnessLevelSearcherCode) inputNat =
    Part.some (BitString.toNatExact x)
  calc
    Nat.Partrec.Code.eval (Classical.choose exists_randomnessLevelSearcherCode) inputNat =
        Nat.rfindOpt (randomnessLevelSearchStepNat inputNat) :=
          eval_randomnessLevelSearcherCode inputNat
    _ = Part.some (BitString.toNatExact x) := Part.eq_some_iff.2 hrfind

private theorem randomnessLevelFeature_isDecoder
    {δ : Program → Nat} {φ : Nat → Program → Nat} {approx pad : Program} {m : Nat}
    (hδ : IsUniformMartinLofTest δ)
    (happrox : IsRandomnessApproximationProgram φ approx)
    (hmono : ∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x) :
    IsRandomnessLevelIndexDecoder δ m (randomnessLevelFeature approx m pad) := by
  intro n x hx
  have hnm : m ≤ n := by
    by_contra hlt
    have hempty : randomnessLevelSet δ n m = [] := hδ.empty_of_length_lt (Nat.lt_of_not_ge hlt)
    simpa [hempty] using hx
  obtain ⟨q0, hq0⟩ := randomnessLevelCandidateAtStep_complete happrox hlim hx
  let q := q0 + 1
  have hqMem : x ∈ randomnessLevelDiscoveredUpToStep approx m n q := by
    rw [show q = q0 + 1 by rfl, randomnessLevelDiscoveredUpToStep_succ, mem_appendIfNew_iff]
    exact Or.inr hq0
  let xs := randomnessLevelDiscoveredUpToStep approx m n q
  let i := xs.idxOf x
  have hiLen : i < xs.length := List.idxOf_lt_length_of_mem hqMem
  have hget : xs[i]? = some x := List.getElem?_idxOf hqMem
  have hiPow : i < 2 ^ (n - m) := by
    have hlen := randomnessLevelDiscoveredUpToStep_length_le hδ happrox hmono hlim
      (approx := approx) (m := m) (n := n) (q := q)
    unfold xs i at hiLen hget
    exact lt_of_lt_of_le hiLen hlen
  refine ⟨i, hiPow, ?_⟩
  exact randomnessLevelFeature_runs_of_searcher
    (approx := approx) (m := m) (pad := pad)
    (payloadInput := ofNatFixed (n - m) i)
    (x := x)
    (randomnessLevelSearcher_runs_of_getElem (approx := approx) (m := m) (n := n)
      (i := i) (q := q) (pad := pad) hiPow hnm hget)

private theorem encodeThreshold_lt_pow (c : Nat) :
    4 * c + 40 < 2 ^ (c + 10) := by
  induction c with
  | zero =>
      decide
  | succ c ih =>
      calc
        4 * (c + 1) + 40 = (4 * c + 40) + 4 := by omega
        _ < 2 ^ (c + 10) + 4 := by omega
        _ ≤ 2 ^ (c + 10) + 2 ^ (c + 10) := by
          have hpow : 4 ≤ 2 ^ (c + 10) := by
            have hge : 2 ≤ c + 10 := by omega
            calc
              4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (c + 10) := by
                exact Nat.pow_le_pow_right (by decide) hge
          exact Nat.add_le_add_left hpow _
        _ = 2 * 2 ^ (c + 10) := by omega
        _ = 2 ^ (c + 11) := by
            simp [Nat.pow_succ', Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

noncomputable def randomnessLevelFeatureBudget (approx : Program) : Nat :=
  BitString.blen approx +
    2 * BitString.blen (BitString.ofNatExact (BitString.blen approx)) +
    randomnessLevelFeaturePlainOverhead + 2

noncomputable def randomnessLevelFeatureThreshold (approx : Program) : Nat :=
  2 ^ (randomnessLevelFeatureBudget approx + 10)

private theorem randomnessLevelFeatureThreshold_pos (approx : Program) :
    0 < randomnessLevelFeatureThreshold approx := by
  simp [randomnessLevelFeatureThreshold]

noncomputable def randomnessLevelFeatureBaseLen (approx : Program) : Nat :=
  BitString.blen (randomnessLevelFeature approx (randomnessLevelFeatureThreshold approx) ([] : Program))

noncomputable def randomnessLevelFeaturePadLen (approx : Program) : Nat :=
  randomnessLevelFeatureThreshold approx - 1 - randomnessLevelFeatureBaseLen approx

noncomputable def randomnessLevelFeaturePad (approx : Program) : Program :=
  List.replicate (randomnessLevelFeaturePadLen approx) false

noncomputable def chosenRandomnessLevelFeature (approx : Program) : Program :=
  randomnessLevelFeature approx (randomnessLevelFeatureThreshold approx) (randomnessLevelFeaturePad approx)

private theorem randomnessLevelFeatureBaseBound (approx : Program) :
    randomnessLevelFeatureBaseLen approx < randomnessLevelFeatureThreshold approx := by
  let c := randomnessLevelFeatureBudget approx
  let m := randomnessLevelFeatureThreshold approx
  let baseLen := randomnessLevelFeatureBaseLen approx
  have hmEnc :
      BitString.blen (BitString.ofNatExact m) ≤ c + 11 := by
    have hmSize : Nat.size m = c + 11 := by
      simp [m, randomnessLevelFeatureThreshold, c, randomnessLevelFeatureBudget, Nat.size_pow]
    exact le_trans (BitString.blen_ofNatExact_le_size m) (by simpa [hmSize])
  have hmEnc2 :
      BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact m))) ≤ c + 11 := by
    have hlt :
        BitString.blen (BitString.ofNatExact m) < 2 ^ (c + 11) := by
      exact lt_of_le_of_lt hmEnc (show c + 11 < 2 ^ (c + 11) from Nat.lt_two_pow_self)
    exact le_trans
      (BitString.blen_ofNatExact_le_size (BitString.blen (BitString.ofNatExact m)))
      (Nat.size_le.2 hlt)
  have hbaseFormula :
      baseLen =
        c + BitString.blen (BitString.ofNatExact m) +
          2 * BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact m))) := by
    rw [show baseLen = BitString.blen (randomnessLevelFeature approx m ([] : Program)) by
      rfl]
    rw [blen_randomnessLevelFeature]
    simp [c, randomnessLevelFeatureBudget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hbaseLe : baseLen ≤ 4 * c + 40 := by
    rw [hbaseFormula]
    omega
  have hthreshold : 4 * c + 40 < m := by
    simpa [m, randomnessLevelFeatureThreshold] using encodeThreshold_lt_pow c
  exact lt_of_le_of_lt hbaseLe hthreshold

@[simp] private theorem blen_randomnessLevelFeaturePad (approx : Program) :
    BitString.blen (randomnessLevelFeaturePad approx) = randomnessLevelFeaturePadLen approx := by
  simp [randomnessLevelFeaturePad, randomnessLevelFeaturePadLen]

set_option maxHeartbeats 5000000 in
private theorem chosenRandomnessLevelFeature_length (approx : Program) :
    BitString.blen (chosenRandomnessLevelFeature approx) =
      randomnessLevelFeatureThreshold approx - 1 := by
  let m := randomnessLevelFeatureThreshold approx
  let baseLen := randomnessLevelFeatureBaseLen approx
  have hbaseFormula :
      baseLen =
        BitString.blen approx + BitString.blen (BitString.ofNatExact m) +
          2 * BitString.blen (BitString.ofNatExact (BitString.blen approx)) +
          2 * BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact m))) +
          randomnessLevelFeaturePlainOverhead + 2 := by
    rw [show baseLen = BitString.blen (randomnessLevelFeature approx m ([] : Program)) by
      rfl]
    rw [blen_randomnessLevelFeature]
    simp
  have hbaseLe : baseLen ≤ m - 1 := by
    have hbaseBound : baseLen < m := by
      simpa [baseLen, m, randomnessLevelFeatureBaseLen, randomnessLevelFeatureThreshold] using
        randomnessLevelFeatureBaseBound approx
    omega
  have hbaseFormula' :
      randomnessLevelFeatureBaseLen approx =
        BitString.blen approx +
          BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)) +
          2 * BitString.blen (BitString.ofNatExact (BitString.blen approx)) +
          2 * BitString.blen
            (BitString.ofNatExact
              (BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)))) +
          randomnessLevelFeaturePlainOverhead + 2 := by
    simpa [baseLen, m, randomnessLevelFeatureBaseLen, randomnessLevelFeatureThreshold] using
      hbaseFormula
  rw [chosenRandomnessLevelFeature, randomnessLevelFeaturePad, blen_randomnessLevelFeature]
  simp [randomnessLevelFeaturePadLen]
  have hrewrite :
      randomnessLevelFeatureThreshold approx - 1 - randomnessLevelFeatureBaseLen approx +
          (BitString.blen approx +
            BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)) +
            2 * BitString.blen (BitString.ofNatExact (BitString.blen approx)) +
            2 * BitString.blen
              (BitString.ofNatExact
                (BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)))) +
            randomnessLevelFeaturePlainOverhead + 2)
        =
          randomnessLevelFeatureThreshold approx - 1 - randomnessLevelFeatureBaseLen approx +
            randomnessLevelFeatureBaseLen approx := by
    simpa [Nat.add_assoc] using congrArg
      (fun t =>
        randomnessLevelFeatureThreshold approx - 1 - randomnessLevelFeatureBaseLen approx + t)
      hbaseFormula'.symm
  calc
    randomnessLevelFeatureThreshold approx - 1 - randomnessLevelFeatureBaseLen approx +
        BitString.blen approx +
          BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)) +
          2 * BitString.blen (BitString.ofNatExact (BitString.blen approx)) +
          2 * BitString.blen
            (BitString.ofNatExact
              (BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)))) +
          randomnessLevelFeaturePlainOverhead +
          2
        =
      randomnessLevelFeatureThreshold approx - 1 - randomnessLevelFeatureBaseLen approx +
        (BitString.blen approx +
          BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)) +
          2 * BitString.blen (BitString.ofNatExact (BitString.blen approx)) +
          2 * BitString.blen
            (BitString.ofNatExact
              (BitString.blen (BitString.ofNatExact (randomnessLevelFeatureThreshold approx)))) +
          randomnessLevelFeaturePlainOverhead +
          2) := by
      ac_rfl
    _ =
      randomnessLevelFeatureThreshold approx - 1 - randomnessLevelFeatureBaseLen approx +
        randomnessLevelFeatureBaseLen approx := hrewrite
    _ = randomnessLevelFeatureThreshold approx - 1 := by
      simpa [randomnessLevelFeaturePadLen] using Nat.sub_add_cancel hbaseLe

private theorem chosenRandomnessLevelFeature_isDecoder
    {δ : Program → Nat} {φ : Nat → Program → Nat} {approx : Program}
    (hδ : IsUniformMartinLofTest δ)
    (happrox : IsRandomnessApproximationProgram φ approx)
    (hmono : ∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x) :
    IsRandomnessLevelIndexDecoder δ (randomnessLevelFeatureThreshold approx)
      (chosenRandomnessLevelFeature approx) := by
  simpa [chosenRandomnessLevelFeature, randomnessLevelFeatureThreshold, randomnessLevelFeaturePad]
    using randomnessLevelFeature_isDecoder
      (hδ := hδ) (happrox := happrox) (hmono := hmono) (hlim := hlim)
      (approx := approx) (m := randomnessLevelFeatureThreshold approx)
      (pad := randomnessLevelFeaturePad approx)

set_option maxHeartbeats 5000000 in
private theorem exists_randomnessLevelFeatureDecoder
    {δ : Program → Nat} {φ : Nat → Program → Nat} {approx : Program}
    (hδ : IsUniformMartinLofTest δ)
    (happrox : IsRandomnessApproximationProgram φ approx)
    (hmono : ∀ {t₁ t₂ x}, t₁ ≤ t₂ → φ t₁ x ≤ φ t₂ x)
    (hlim : ∀ x, ∃ T, ∀ {t}, T ≤ t → φ t x = δ x) :
    ∃ f : Program, ∃ m : Nat,
      BitString.blen f = m - 1 ∧ 0 < m ∧ IsRandomnessLevelIndexDecoder δ m f := by
  exact ⟨chosenRandomnessLevelFeature approx, randomnessLevelFeatureThreshold approx,
    chosenRandomnessLevelFeature_length approx,
    randomnessLevelFeatureThreshold_pos approx,
    chosenRandomnessLevelFeature_isDecoder hδ happrox hmono hlim⟩

/-- Paper-form Theorem 5.2. From a uniform unbounded Martin-Löf test we obtain a single feature
that is a feature of every string whose deficiency exceeds the feature length. -/
theorem theorem52 {δ : Program → Nat}
    (hδ : IsUniformMartinLofTest δ)
    (hunbounded : IsUnboundedMartinLofTest δ) :
    ∃ f : Program, ∀ x : Program, BitString.blen f < δ x → IsFeature runs f x := by
  rcases hδ.lowerSemicomputable with ⟨φ, hφcomp, hmono, hlim⟩
  obtain ⟨approx, happrox⟩ := exists_randomnessApproximationProgram hφcomp
  rcases exists_randomnessLevelFeatureDecoder hδ happrox hmono hlim with
    ⟨f, m, hfLen, hmPos, hdecoder⟩
  have _hnonvacuous : ∃ x : Program, BitString.blen f < δ x := by
    simpa [hfLen] using hunbounded (BitString.blen f)
  refine ⟨f, ?_⟩
  intro x hx
  have hxm : m ≤ δ x := by
    rw [hfLen] at hx
    omega
  have hgap : BitString.blen f < m := by
    rw [hfLen]
    omega
  exact randomnessLevelIndexDecoder_isFeature_of_lengthGap hδ hdecoder hgap hxm

end

end Compression

end IcTheory
