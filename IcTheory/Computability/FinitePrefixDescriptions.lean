import IcTheory.Computability.PrefixInformation
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.ReduceOption
import Mathlib.Tactic

namespace IcTheory

namespace BitString

theorem pair_eq_pair_iff {x₁ y₁ x₂ y₂ : BitString} :
    pair x₁ y₁ = pair x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    have hlen : blen x₁ = blen x₂ := by
      simpa [pair, e1] using congrArg countLeadingTrue h
    have hsplit : splitAt (blen x₁ + 1) (pair x₁ y₁) = splitAt (blen x₁ + 1) (pair x₂ y₂) := by
      simpa [h]
    have hrest : x₁ ++ y₁ = x₂ ++ y₂ := by
      have := congrArg Prod.snd hsplit
      simpa [pair, e1, hlen, splitAt_eq_take_drop] using this
    have hsplitRest : splitAt (blen x₁) (x₁ ++ y₁) = splitAt (blen x₁) (x₂ ++ y₂) := by
      simpa [hrest]
    have hx : x₁ = x₂ := by
      have := congrArg Prod.fst hsplitRest
      simpa [hlen, splitAt_eq_take_drop] using this
    have hy : y₁ = y₂ := by
      have := congrArg Prod.snd hsplitRest
      simpa [hlen, splitAt_eq_take_drop, hx] using this
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem e2_injective : Function.Injective e2 := by
  intro x y h
  have hlen :
      blen (ofNat (blen x)) = blen (ofNat (blen y)) := by
    simpa [e2, e1] using congrArg countLeadingTrue h
  have hsplit :
      splitAt (blen (ofNat (blen x)) + 1) (e2 x) =
        splitAt (blen (ofNat (blen x)) + 1) (e2 y) := by
    simpa [h]
  have hrest : ofNat (blen x) ++ x = ofNat (blen y) ++ y := by
    have := congrArg Prod.snd hsplit
    simpa [e2, e1, hlen, splitAt_eq_take_drop] using this
  have hsplitRest :
      splitAt (blen (ofNat (blen x))) (ofNat (blen x) ++ x) =
        splitAt (blen (ofNat (blen x))) (ofNat (blen y) ++ y) := by
    simpa [hrest]
  have hx : x = y := by
    have := congrArg Prod.snd hsplitRest
    simpa [hlen, splitAt_eq_take_drop] using this
  exact hx

end BitString

namespace UniversalMachine

theorem runs_deterministic {p input x y : Program}
    (hx : runs p input x) (hy : runs p input y) :
    x = y := by
  apply BitString.toNatExact_injective
  have h' : Part.some (BitString.toNatExact x) = Part.some (BitString.toNatExact y) := by
    calc
      Part.some (BitString.toNatExact x) =
          Nat.Partrec.Code.eval (programToCode p) (BitString.toNatExact input) := by
            simpa [runs] using hx.symm
      _ = Part.some (BitString.toNatExact y) := by
            simpa [runs] using hy
  simpa using h'

theorem prefixRuns_deterministic {p input x y : Program}
    (hx : PrefixRuns p input x) (hy : PrefixRuns p input y) :
    x = y := by
  rcases hx with ⟨fx, sx, hpx, hrx⟩
  rcases hy with ⟨fy, sy, hpy, hry⟩
  have hp : BitString.pair fx (BitString.e2 sx) = BitString.pair fy (BitString.e2 sy) := by
    exact hpx.symm.trans hpy
  have hpair := (BitString.pair_eq_pair_iff.mp hp)
  have hf : fx = fy := hpair.1
  have hs : sx = sy := BitString.e2_injective hpair.2
  subst hf hs
  exact runs_deterministic hrx hry

/-- Canonical output chosen for a prefix description, when it has one. -/
noncomputable def prefixOutput (p input : Program) : Option Program := by
  classical
  by_cases h : ∃ output, PrefixRuns p input output
  · exact some (Classical.choose h)
  · exact none

theorem prefixOutput_eq_some_of_prefixRuns {p input output : Program}
    (hp : PrefixRuns p input output) :
    prefixOutput p input = some output := by
  classical
  unfold prefixOutput
  split_ifs with h
  · have hchoose : Classical.choose h = output :=
      prefixRuns_deterministic (Classical.choose_spec h) hp
    simp [hchoose]
  · exact False.elim (h ⟨output, hp⟩)

theorem prefixRuns_of_prefixOutput_eq_some {p input output : Program}
    (hpo : prefixOutput p input = some output) :
    PrefixRuns p input output := by
  classical
  unfold prefixOutput at hpo
  split_ifs at hpo with h
  · have hchoose : Classical.choose h = output := by
      simpa using hpo
    exact hchoose ▸ Classical.choose_spec h

@[simp] theorem prefixOutput_eq_some_iff {p input output : Program} :
    prefixOutput p input = some output ↔ PrefixRuns p input output := by
  constructor
  · exact prefixRuns_of_prefixOutput_eq_some
  · exact prefixOutput_eq_some_of_prefixRuns

/-- Bounded evaluation of a plain program at fuel `k`, returning an exact bitstring output when
the evaluator succeeds within that bound. -/
def prefixOutputAtFuel (k : Nat) (p input : Program) : Option Program :=
  (Nat.Partrec.Code.evaln k (programToCode p) (BitString.toNatExact input)).map BitString.ofNatExact

theorem prefixOutputAtFuel_sound {k : Nat} {p input output : Program}
    (h : prefixOutputAtFuel k p input = some output) :
    runs p input output := by
  rw [prefixOutputAtFuel, Option.map_eq_some_iff] at h
  rcases h with ⟨outputNat, hout, rfl⟩
  have hEval :
      outputNat ∈ Nat.Partrec.Code.eval (programToCode p) (BitString.toNatExact input) :=
    Nat.Partrec.Code.evaln_sound hout
  have hEq :
      Nat.Partrec.Code.eval (programToCode p) (BitString.toNatExact input) = Part.some outputNat :=
    Part.eq_some_iff.2 hEval
  simpa [runs] using hEq

theorem prefixOutputAtFuel_complete {p input output : Program}
    (h : runs p input output) :
    ∃ k, prefixOutputAtFuel k p input = some output := by
  have hEval :
      BitString.toNatExact output ∈
        Nat.Partrec.Code.eval (programToCode p) (BitString.toNatExact input) := by
    exact Part.eq_some_iff.1 (by simpa [runs] using h)
  rcases (Nat.Partrec.Code.evaln_complete.mp hEval) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [prefixOutputAtFuel, Option.map_eq_some_iff]
  exact ⟨BitString.toNatExact output, hk, by simp⟩

theorem packedInput_primrec : Primrec₂ packedInput := by
  refine (BitString.ofNatExact_primrec.comp
    (Primrec₂.natPair.comp
      (BitString.toNatExact_primrec.comp Primrec.fst)
      (BitString.toNatExact_primrec.comp Primrec.snd))).to₂.of_eq ?_
  intro input payload
  rfl

theorem packedInput_computable : Computable₂ packedInput :=
  packedInput_primrec.to_comp

private theorem natSize_primrec : Primrec Nat.size := by
  have hlen : Primrec fun p : Unit × List Nat => p.2.length :=
    Primrec.list_length.comp Primrec.snd
  have hindex : Primrec₂ fun (_ : Unit × List Nat) (n : Nat) =>
      if Nat.bodd n then n.div2 + 1 else n.div2 := by
    let hindex0 : Primrec fun p : (Unit × List Nat) × Nat =>
        bif Nat.bodd p.2 then p.2.div2 + 1 else p.2.div2 :=
      Primrec.cond
        (Primrec.nat_bodd.comp Primrec.snd)
        (Primrec.nat_add.comp (Primrec.nat_div2.comp Primrec.snd) (Primrec.const 1))
        (Primrec.nat_div2.comp Primrec.snd)
    exact hindex0.of_eq fun p => by simp [Bool.cond_eq_ite]
  have hstep : Primrec₂ fun (a : Unit × List Nat) (n : Nat) =>
      Option.map Nat.succ (a.2[if Nat.bodd n then n.div2 + 1 else n.div2]?) := by
    exact Primrec.option_map
      (hf := Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) hindex)
      (hg := (Primrec.succ.comp Primrec.snd).to₂)
  have hmatch : Primrec₂ fun (_ : Unit) (prevs : List Nat) =>
      match prevs.length with
      | 0 => (some 0 : Option Nat)
      | n + 1 => Option.map Nat.succ (prevs[if Nat.bodd n then n.div2 + 1 else n.div2]?) := by
    let hmatch0 : Primrec fun a : Unit × List Nat =>
        Nat.casesOn (motive := fun _ => Option Nat) a.2.length (some 0)
          (fun n => Option.map Nat.succ (a.2[if Nat.bodd n then n.div2 + 1 else n.div2]?)) :=
      Primrec.nat_casesOn hlen (Primrec.const (some 0 : Option Nat)) hstep
    refine hmatch0.of_eq ?_
    intro a
    cases h : a.2.length with
    | zero =>
        simp [h]
    | succ n =>
        simp [h]
  have h : Primrec₂ (fun (_ : Unit) n => Nat.size n) := by
    refine Primrec.nat_strong_rec (f := fun (_ : Unit) n => Nat.size n) hmatch ?_
    intro _ n
    cases n with
    | zero =>
        simp [hmatch, Nat.size]
    | succ n =>
        let i := if Nat.bodd n then n.div2 + 1 else n.div2
        have hidx : i < n + 1 := by
          cases hb : Nat.bodd n
          · have h0 : n = 2 * n.div2 := by
              simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
            simp [i, hb]
            simpa [Nat.div2_val] using Nat.div_le_self n 2
          · have h1 : n = 2 * n.div2 + 1 := by
              simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
            simp [i, hb]
            omega
        have hget : (((List.range (n + 1)).map Nat.size)[i]?) = some (Nat.size i) := by
          rw [List.getElem?_map, List.getElem?_range hidx]
          simp
        have hsize : Nat.size (n + 1) = Nat.succ (Nat.size i) := by
          cases hb : Nat.bodd n
          · have h0 : n = 2 * n.div2 := by
              simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
            have hi : i = n.div2 := by
              simp [i, hb]
            have hbit : n + 1 = Nat.bit true n.div2 := by
              nth_rewrite 1 [h0]
              calc
                (2 * n.div2) + 1 = 2 * n.div2 + 1 := by rfl
                _ = Nat.bit true n.div2 := by simp [Nat.bit_val]
            have hne : Nat.bit true n.div2 ≠ 0 := by
              simp [Nat.bit_val]
            rw [hi, hbit, Nat.size_bit hne]
          · have h1 : n = 2 * n.div2 + 1 := by
              simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
            have hi : i = n.div2 + 1 := by
              simp [i, hb]
            have hbit : n + 1 = Nat.bit false (n.div2 + 1) := by
              nth_rewrite 1 [h1]
              calc
                (2 * n.div2 + 1) + 1 = 2 * (n.div2 + 1) := by omega
                _ = Nat.bit false (n.div2 + 1) := by simp [Nat.bit_val]
            have hne : Nat.bit false (n.div2 + 1) ≠ 0 := by
              simp [Nat.bit_val]
            rw [hi, hbit, Nat.size_bit hne]
        simp [hmatch, List.length_range, i, hsize, hget]
  simpa using h.comp (Primrec.const Unit.unit) Primrec.id

private theorem natSize_computable : Computable Nat.size :=
  natSize_primrec.to_comp

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

private theorem allUpToLength_computable : Computable BitString.allUpToLength :=
  allUpToLength_primrec.to_comp

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

private theorem prefixOutputAtFuel_computable :
    Computable fun a : Nat × Program × Program =>
      prefixOutputAtFuel a.1 a.2.1 a.2.2 :=
  prefixOutputAtFuel_primrec.to_comp

/-- Finite list of all outputs produced from `input` by prefix descriptions of length at most
`n`. -/
noncomputable def prefixOutputsUpToLength (input : Program) (n : Nat) : List Program :=
  ((BitString.allUpToLength n).filterMap fun p => prefixOutput p input).dedup

theorem nodup_prefixOutputsUpToLength (input : Program) (n : Nat) :
    (prefixOutputsUpToLength input n).Nodup := by
  unfold prefixOutputsUpToLength
  exact List.nodup_dedup _

private theorem length_filterMap_le {α β : Type} (f : α → Option β) :
    ∀ l : List α, (l.filterMap f).length ≤ l.length
  | [] => by simp
  | a :: l => by
      cases h : f a with
      | none =>
          simpa [List.filterMap, h] using Nat.le_succ_of_le (length_filterMap_le f l)
      | some b =>
          simpa [List.filterMap, h] using Nat.succ_le_succ (length_filterMap_le f l)

theorem mem_prefixOutputsUpToLength_of_prefixRuns {p input output : Program} {n : Nat}
    (hlen : BitString.blen p ≤ n)
    (hp : PrefixRuns p input output) :
    output ∈ prefixOutputsUpToLength input n := by
  unfold prefixOutputsUpToLength
  rw [List.mem_dedup, List.mem_filterMap]
  exact ⟨p, by simpa using (BitString.mem_allUpToLength_iff.mpr hlen), by simpa using hp⟩

theorem length_prefixOutputsUpToLength_le (input : Program) (n : Nat) :
    (prefixOutputsUpToLength input n).length ≤ 2 ^ (n + 1) - 1 := by
  unfold prefixOutputsUpToLength
  calc
    ((BitString.allUpToLength n).filterMap fun p => prefixOutput p input).dedup.length ≤
        ((BitString.allUpToLength n).filterMap fun p => prefixOutput p input).length := by
      exact List.Sublist.length_le (List.dedup_sublist _)
    _ ≤ (BitString.allUpToLength n).length := by
      exact length_filterMap_le (fun p => prefixOutput p input) (BitString.allUpToLength n)
    _ = 2 ^ (n + 1) - 1 := by simp

/-- Finite witness family for prefix descriptions of length at most `n`, exposed as
interpreter/payload pairs. This is the machine-facing search space for later dovetailing
arguments. -/
def prefixWitnessPairsUpToLength (n : Nat) : List (Program × Program) :=
  (BitString.allUpToLength n).flatMap fun f =>
    (BitString.allUpToLength n).filterMap fun s =>
      if BitString.blen (BitString.pair f (BitString.e2 s)) ≤ n then some (f, s) else none

private theorem prefixWitnessPairsUpToLength_primrec :
    Primrec prefixWitnessPairsUpToLength := by
  have hinner : Primrec fun a : Nat × Program =>
      (BitString.allUpToLength a.1).filterMap fun s =>
        if 2 * BitString.blen a.2 + (2 * Nat.size (BitString.blen s) + BitString.blen s + 1) < a.1
        then some (a.2, s)
        else none := by
    have hpred : PrimrecPred fun p : (Nat × Program) × Program =>
        2 * BitString.blen p.1.2 + (2 * Nat.size (BitString.blen p.2) + BitString.blen p.2 + 1) <
          p.1.1 := by
      have hlenF : Primrec fun p : (Nat × Program) × Program => BitString.blen p.1.2 := by
        exact Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)
      have hlenS : Primrec fun p : (Nat × Program) × Program => BitString.blen p.2 := by
        exact Primrec.list_length.comp Primrec.snd
      have hsizeS : Primrec fun p : (Nat × Program) × Program => Nat.size (BitString.blen p.2) := by
        exact natSize_primrec.comp hlenS
      have hdoubleF : Primrec fun p : (Nat × Program) × Program => 2 * BitString.blen p.1.2 := by
        exact Primrec.nat_mul.comp (Primrec.const 2) hlenF
      have hdoubleSize :
          Primrec fun p : (Nat × Program) × Program => 2 * Nat.size (BitString.blen p.2) := by
        exact Primrec.nat_mul.comp (Primrec.const 2) hsizeS
      have hsum₁ :
          Primrec fun p : (Nat × Program) × Program =>
            2 * Nat.size (BitString.blen p.2) + BitString.blen p.2 := by
        exact Primrec.nat_add.comp hdoubleSize hlenS
      have hsum₂ :
          Primrec fun p : (Nat × Program) × Program =>
            2 * Nat.size (BitString.blen p.2) + BitString.blen p.2 + 1 := by
        exact Primrec.nat_add.comp hsum₁ (Primrec.const 1)
      have hlhs :
          Primrec fun p : (Nat × Program) × Program =>
            2 * BitString.blen p.1.2 + (2 * Nat.size (BitString.blen p.2) + BitString.blen p.2 + 1) := by
        exact Primrec.nat_add.comp hdoubleF hsum₂
      exact Primrec.nat_lt.comp hlhs (Primrec.fst.comp Primrec.fst)
    have hsome :
        Primrec fun p : (Nat × Program) × Program => some (p.1.2, p.2) := by
      exact Primrec.option_some.comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
    have hguard :
        Primrec fun p : (Nat × Program) × Program =>
          if 2 * BitString.blen p.1.2 + (2 * Nat.size (BitString.blen p.2) + BitString.blen p.2 + 1) <
              p.1.1
          then some (p.1.2, p.2)
          else none := by
      exact Primrec.ite hpred hsome (Primrec.const none)
    refine (Primrec.listFilterMap
      (hf := allUpToLength_primrec.comp Primrec.fst)
      (hg := hguard.to₂)).of_eq ?_
    intro a
    simp [BitString.blen_e2, BitString.blen_ofNat_eq_size]
  exact (Primrec.list_flatMap allUpToLength_primrec hinner.to₂).of_eq fun n => by
    simp [prefixWitnessPairsUpToLength]

private theorem prefixWitnessPairsUpToLength_computable :
    Computable prefixWitnessPairsUpToLength :=
  prefixWitnessPairsUpToLength_primrec.to_comp

theorem mem_prefixWitnessPairsUpToLength_iff {f s : Program} {n : Nat} :
    (f, s) ∈ prefixWitnessPairsUpToLength n ↔
      BitString.blen (BitString.pair f (BitString.e2 s)) ≤ n := by
  constructor
  · intro h
    unfold prefixWitnessPairsUpToLength at h
    rw [List.mem_flatMap] at h
    rcases h with ⟨f', hf', hs⟩
    rw [List.mem_filterMap] at hs
    rcases hs with ⟨s', hs', hfs⟩
    split_ifs at hfs with hlen
    · rcases hfs with ⟨rfl, rfl⟩
      exact hlen
  · intro hlen
    unfold prefixWitnessPairsUpToLength
    rw [List.mem_flatMap]
    refine ⟨f, ?_, ?_⟩
    · exact (BitString.mem_allUpToLength_iff.mpr (by
        have hf : BitString.blen f ≤ BitString.blen (BitString.pair f (BitString.e2 s)) := by
          simp [BitString.blen_pair]
          omega
        exact le_trans hf hlen))
    · rw [List.mem_filterMap]
      refine ⟨s, ?_, ?_⟩
      · exact (BitString.mem_allUpToLength_iff.mpr (by
          have hs : BitString.blen s ≤ BitString.blen (BitString.pair f (BitString.e2 s)) := by
            simp [BitString.blen_pair, BitString.blen_e2]
            omega
          exact le_trans hs hlen))
      · rw [if_pos hlen]

theorem mem_prefixOutputsUpToLength_iff_existsWitness {x input : Program} {n : Nat} :
    x ∈ prefixOutputsUpToLength input n ↔
      ∃ f s, (f, s) ∈ prefixWitnessPairsUpToLength n ∧ runs f (packedInput input s) x := by
  constructor
  · intro hx
    unfold prefixOutputsUpToLength at hx
    rw [List.mem_dedup, List.mem_filterMap] at hx
    rcases hx with ⟨p, hpLen, hpo⟩
    have hpRuns : PrefixRuns p input x := (prefixOutput_eq_some_iff.mp hpo)
    rcases hpRuns with ⟨f, s, hpEq, hrun⟩
    refine ⟨f, s, ?_, hrun⟩
    rw [mem_prefixWitnessPairsUpToLength_iff]
    rw [← hpEq]
    exact (BitString.mem_allUpToLength_iff.mp hpLen)
  · rintro ⟨f, s, hfs, hrun⟩
    exact mem_prefixOutputsUpToLength_of_prefixRuns
      (input := input) (n := n)
      (p := BitString.pair f (BitString.e2 s))
      (output := x)
      (mem_prefixWitnessPairsUpToLength_iff.mp hfs)
      ⟨f, s, rfl, hrun⟩

theorem mem_prefixOutputsUpToLength_of_prefixConditionalComplexity_le {x input : Program} {n : Nat}
    (hx : PrefixConditionalComplexity x input ≤ n) :
    x ∈ prefixOutputsUpToLength input n := by
  obtain ⟨p, hpLen, hpRuns⟩ := exists_program_forPrefixConditionalComplexity x input
  exact mem_prefixOutputsUpToLength_of_prefixRuns (input := input) (n := n)
    (p := p) (output := x) (by omega) hpRuns

theorem mem_prefixOutputsUpToLength_of_prefixComplexity_le {x : Program} {n : Nat}
    (hx : PrefixComplexity x ≤ n) :
    x ∈ prefixOutputsUpToLength [] n := by
  simpa [PrefixComplexity] using
    (mem_prefixOutputsUpToLength_of_prefixConditionalComplexity_le
      (x := x) (input := ([] : Program)) hx)

theorem mem_prefixOutputsUpToLength_of_jointComplexity_le {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    packedInput x y ∈ prefixOutputsUpToLength [] n := by
  simpa [JointComplexity] using
    (mem_prefixOutputsUpToLength_of_prefixComplexity_le (x := packedInput x y) hxy)

theorem jointComplexity_le_iff_existsWitness {x y : Program} {n : Nat} :
    JointComplexity x y ≤ n ↔
      ∃ f s, (f, s) ∈ prefixWitnessPairsUpToLength n ∧
        runs f (packedInput [] s) (packedInput x y) := by
  constructor
  · intro hxy
    exact (mem_prefixOutputsUpToLength_iff_existsWitness
      (x := packedInput x y) (input := ([] : Program)) (n := n)).mp
      (mem_prefixOutputsUpToLength_of_jointComplexity_le hxy)
  · rintro ⟨f, s, hfs, hrun⟩
    have hpRuns :
        PrefixRuns (BitString.pair f (BitString.e2 s)) [] (packedInput x y) := by
      exact ⟨f, s, rfl, hrun⟩
    have hpLen : BitString.blen (BitString.pair f (BitString.e2 s)) ≤ n :=
      mem_prefixWitnessPairsUpToLength_iff.mp hfs
    have hPrefix :
        PrefixComplexity (packedInput x y) ≤
          BitString.blen (BitString.pair f (BitString.e2 s)) := by
      simpa [PrefixComplexity] using prefixConditionalComplexity_le_length hpRuns
    simpa [JointComplexity] using le_trans hPrefix hpLen

/-- Decode a packed pair back into its two exact bitstring components. -/
def unpackInput (z : Program) : Program × Program :=
  let n := BitString.toNatExact z
  (BitString.ofNatExact n.unpair.1, BitString.ofNatExact n.unpair.2)

private theorem unpackInput_primrec : Primrec unpackInput := by
  refine (Primrec.pair
      (BitString.ofNatExact_primrec.comp
        (Primrec.fst.comp (Primrec.unpair.comp BitString.toNatExact_primrec)))
      (BitString.ofNatExact_primrec.comp
        (Primrec.snd.comp (Primrec.unpair.comp BitString.toNatExact_primrec)))).of_eq ?_
  intro z
  rfl

private theorem unpackInput_computable : Computable unpackInput :=
  unpackInput_primrec.to_comp

@[simp] theorem unpackInput_packedInput (x y : Program) :
    unpackInput (packedInput x y) = (x, y) := by
  simp [unpackInput, toNatExact_packedInput]

@[simp] theorem packedInput_unpackInput (z : Program) :
    packedInput (unpackInput z).1 (unpackInput z).2 = z := by
  apply BitString.toNatExact_injective
  simp [unpackInput, toNatExact_packedInput]

/-- For fixed left component `x`, this is the finite family of right components appearing in
joint descriptions of complexity at most `n`. -/
noncomputable def jointRightOutputsUpToLength (x : Program) (n : Nat) : List Program :=
  ((prefixOutputsUpToLength [] n).filterMap fun z =>
    let w := unpackInput z
    if w.1 = x then some w.2 else none).dedup

theorem nodup_jointRightOutputsUpToLength (x : Program) (n : Nat) :
    (jointRightOutputsUpToLength x n).Nodup := by
  unfold jointRightOutputsUpToLength
  exact List.nodup_dedup _

theorem mem_jointRightOutputsUpToLength_of_jointComplexity_le {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    y ∈ jointRightOutputsUpToLength x n := by
  unfold jointRightOutputsUpToLength
  rw [List.mem_dedup, List.mem_filterMap]
  refine ⟨packedInput x y, mem_prefixOutputsUpToLength_of_jointComplexity_le hxy, ?_⟩
  simp

theorem mem_prefixOutputsUpToLength_of_mem_jointRightOutputsUpToLength {x y : Program} {n : Nat}
    (hy : y ∈ jointRightOutputsUpToLength x n) :
    packedInput x y ∈ prefixOutputsUpToLength [] n := by
  unfold jointRightOutputsUpToLength at hy
  rw [List.mem_dedup, List.mem_filterMap] at hy
  rcases hy with ⟨z, hz, hxy⟩
  simp at hxy
  rcases hxy with ⟨hx, hy⟩
  have hz' : z = packedInput x y := by
    calc
      z = packedInput (unpackInput z).1 (unpackInput z).2 := by
        simpa using (packedInput_unpackInput z).symm
      _ = packedInput x y := by simpa [hx, hy]
  simpa [hz'] using hz

theorem length_jointRightOutputsUpToLength_le (x : Program) (n : Nat) :
    (jointRightOutputsUpToLength x n).length ≤ 2 ^ (n + 1) - 1 := by
  unfold jointRightOutputsUpToLength
  calc
    ((prefixOutputsUpToLength [] n).filterMap
        (fun z =>
          let w := unpackInput z
          if w.1 = x then some w.2 else none)).dedup.length ≤
        ((prefixOutputsUpToLength [] n).filterMap
          (fun z =>
            let w := unpackInput z
            if w.1 = x then some w.2 else none)).length := by
      exact List.Sublist.length_le (List.dedup_sublist _)
    _ ≤ (prefixOutputsUpToLength [] n).length := by
      exact length_filterMap_le
        (fun z =>
          let w := unpackInput z
          if w.1 = x then some w.2 else none)
        (prefixOutputsUpToLength [] n)
    _ ≤ 2 ^ (n + 1) - 1 := by
      exact length_prefixOutputsUpToLength_le [] n

/-- The `t`-th joint-right discovery attempt, using `t.unpair.1` as bounded-evaluation fuel and
`t.unpair.2` as an index into the finite witness family. -/
def jointRightCandidateAtStep (x : Program) (n t : Nat) : Option Program :=
  ((prefixWitnessPairsUpToLength n)[t.unpair.2]?).bind fun w =>
    (prefixOutputAtFuel t.unpair.1 w.1 (packedInput [] w.2)).bind fun z =>
      let xy := unpackInput z
      if xy.1 = x then some xy.2 else none

theorem jointRightCandidateAtStep_sound {x y : Program} {n t : Nat}
    (h : jointRightCandidateAtStep x n t = some y) :
    JointComplexity x y ≤ n := by
  unfold jointRightCandidateAtStep at h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨w, hw, hrest⟩
  rcases w with ⟨f, s⟩
  rw [Option.bind_eq_some_iff] at hrest
  rcases hrest with ⟨z, hz, hxy⟩
  have hfs : (f, s) ∈ prefixWitnessPairsUpToLength n := by
    rw [List.mem_iff_getElem?]
    exact ⟨t.unpair.2, hw⟩
  have hruns : runs f (packedInput [] s) z :=
    prefixOutputAtFuel_sound hz
  have hx : (unpackInput z).1 = x := by
    by_cases hleft : (unpackInput z).1 = x
    · simpa [hleft] using hxy
    · simp [hleft] at hxy
  have hy : (unpackInput z).2 = y := by
    by_cases hleft : (unpackInput z).1 = x
    · simpa [hleft] using hxy
    · simp [hleft] at hxy
  have hzxy : z = packedInput x y := by
    calc
      z = packedInput (unpackInput z).1 (unpackInput z).2 := by
        simpa using (packedInput_unpackInput z).symm
      _ = packedInput x y := by simpa [hx, hy]
  exact (jointComplexity_le_iff_existsWitness (x := x) (y := y) (n := n)).mpr
    ⟨f, s, hfs, by simpa [hzxy] using hruns⟩

theorem jointRightCandidateAtStep_complete {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    ∃ t, jointRightCandidateAtStep x n t = some y := by
  rcases (jointComplexity_le_iff_existsWitness (x := x) (y := y) (n := n)).mp hxy with
    ⟨f, s, hfs, hrun⟩
  rw [List.mem_iff_getElem?] at hfs
  rcases hfs with ⟨j, hj⟩
  rcases prefixOutputAtFuel_complete hrun with ⟨k, hk⟩
  refine ⟨Nat.pair k j, ?_⟩
  simp [jointRightCandidateAtStep, Nat.unpair_pair, hj, hk, unpackInput_packedInput]

/-- The same bounded witness/fuel scan, but returning the packed joint output directly before any
left-component filtering. -/
def jointPackedCandidateAtStep (n t : Nat) : Option Program :=
  ((prefixWitnessPairsUpToLength n)[t.unpair.2]?).bind fun w =>
    prefixOutputAtFuel t.unpair.1 w.1 (packedInput [] w.2)

theorem jointPackedCandidateAtStep_sound {n t : Nat} {z : Program}
    (h : jointPackedCandidateAtStep n t = some z) :
    JointComplexity (unpackInput z).1 (unpackInput z).2 ≤ n := by
  unfold jointPackedCandidateAtStep at h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨w, hw, hz⟩
  rcases w with ⟨f, s⟩
  have hfs : (f, s) ∈ prefixWitnessPairsUpToLength n := by
    rw [List.mem_iff_getElem?]
    exact ⟨t.unpair.2, hw⟩
  have hruns : runs f (packedInput [] s) z :=
    prefixOutputAtFuel_sound hz
  have hzxy : z = packedInput (unpackInput z).1 (unpackInput z).2 := by
    simpa using (packedInput_unpackInput z).symm
  have hruns' : runs f (packedInput [] s) (packedInput (unpackInput z).1 (unpackInput z).2) := by
    rwa [hzxy] at hruns
  exact (jointComplexity_le_iff_existsWitness
    (x := (unpackInput z).1) (y := (unpackInput z).2) (n := n)).mpr
      ⟨f, s, hfs, hruns'⟩

theorem jointPackedCandidateAtStep_complete {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    ∃ t, jointPackedCandidateAtStep n t = some (packedInput x y) := by
  rcases (jointComplexity_le_iff_existsWitness (x := x) (y := y) (n := n)).mp hxy with
    ⟨f, s, hfs, hrun⟩
  rw [List.mem_iff_getElem?] at hfs
  rcases hfs with ⟨j, hj⟩
  rcases prefixOutputAtFuel_complete hrun with ⟨k, hk⟩
  refine ⟨Nat.pair k j, ?_⟩
  simp [jointPackedCandidateAtStep, Nat.unpair_pair, hj, hk]

private theorem jointPackedCandidateAtStep_primrec :
    Primrec fun a : Nat × Nat => jointPackedCandidateAtStep a.1 a.2 := by
  have hfuel : Primrec fun a : Nat × Nat => a.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hindex : Primrec fun a : Nat × Nat => a.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hwitness :
      Primrec fun a : Nat × Nat =>
        (prefixWitnessPairsUpToLength a.1)[a.2.unpair.2]? :=
    Primrec.list_getElem?.comp
      (prefixWitnessPairsUpToLength_primrec.comp Primrec.fst)
      hindex
  have hrunArg :
      Primrec fun p : (Nat × Nat) × (Program × Program) =>
        (p.1.2.unpair.1, p.2.1, packedInput [] p.2.2) := by
    refine Primrec.pair (hfuel.comp Primrec.fst) ?_
    refine Primrec.pair (Primrec.fst.comp Primrec.snd) ?_
    exact packedInput_primrec.comp
      (Primrec.const ([] : Program))
      (Primrec.snd.comp Primrec.snd)
  have hrun :
      Primrec₂ fun (a : Nat × Nat) (w : Program × Program) =>
        prefixOutputAtFuel a.2.unpair.1 w.1 (packedInput [] w.2) :=
    (prefixOutputAtFuel_primrec.comp hrunArg).to₂
  exact (Primrec.option_bind hwitness hrun).of_eq fun a => by
    cases a with
    | mk n t =>
        simp [jointPackedCandidateAtStep]

private theorem jointPackedCandidateAtStep_computable :
    Computable fun a : Nat × Nat => jointPackedCandidateAtStep a.1 a.2 :=
  jointPackedCandidateAtStep_primrec.to_comp

private theorem jointRightCandidateAtStep_primrec :
    Primrec fun a : Program × Nat × Nat => jointRightCandidateAtStep a.1 a.2.1 a.2.2 := by
  have hfuel : Primrec fun a : Program × Nat × Nat => a.2.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hindex : Primrec fun a : Program × Nat × Nat => a.2.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hwitness :
      Primrec fun a : Program × Nat × Nat =>
        (prefixWitnessPairsUpToLength a.2.1)[a.2.2.unpair.2]? :=
    Primrec.list_getElem?.comp
      (prefixWitnessPairsUpToLength_primrec.comp (Primrec.fst.comp Primrec.snd))
      hindex
  have hrunArg :
      Primrec fun p : (Program × Nat × Nat) × (Program × Program) =>
        (p.1.2.2.unpair.1, p.2.1, packedInput [] p.2.2) := by
    refine Primrec.pair (hfuel.comp Primrec.fst) ?_
    refine Primrec.pair (Primrec.fst.comp Primrec.snd) ?_
    exact packedInput_primrec.comp
      (Primrec.const ([] : Program))
      (Primrec.snd.comp Primrec.snd)
  have hrun :
      Primrec₂ fun (a : Program × Nat × Nat) (w : Program × Program) =>
        prefixOutputAtFuel a.2.2.unpair.1 w.1 (packedInput [] w.2) :=
    (prefixOutputAtFuel_primrec.comp hrunArg).to₂
  have hsameLeft :
      PrimrecPred fun p : (Program × Nat × Nat) × Program =>
        (unpackInput p.2).1 = p.1.1 := by
    exact PrimrecRel.comp (Primrec.eq : PrimrecRel (fun x y : Program => x = y))
      (Primrec.fst.comp (unpackInput_primrec.comp Primrec.snd))
      (Primrec.fst.comp Primrec.fst)
  have hsomeRight :
      Primrec fun p : (Program × Nat × Nat) × Program =>
        some ((unpackInput p.2).2) :=
    Primrec.option_some.comp (Primrec.snd.comp (unpackInput_primrec.comp Primrec.snd))
  have hselect :
      Primrec₂ fun (a : Program × Nat × Nat) (z : Program) =>
        if (unpackInput z).1 = a.1 then some (unpackInput z).2 else none := by
    exact (Primrec.ite hsameLeft hsomeRight (Primrec.const (Option.none : Option Program))).to₂
  have hinnerSelect :
      Primrec₂ fun (p : (Program × Nat × Nat) × (Program × Program)) (z : Program) =>
        if (unpackInput z).1 = p.1.1 then some (unpackInput z).2 else none :=
    hselect.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hinner :
      Primrec fun p : (Program × Nat × Nat) × (Program × Program) =>
        (prefixOutputAtFuel p.1.2.2.unpair.1 p.2.1 (packedInput [] p.2.2)).bind fun z =>
          if (unpackInput z).1 = p.1.1 then some (unpackInput z).2 else none :=
    Primrec.option_bind hrun hinnerSelect
  exact (Primrec.option_bind hwitness hinner.to₂).of_eq fun a => by
    cases a with
    | mk x ni =>
        cases ni with
        | mk n t =>
            simp [jointRightCandidateAtStep]

private theorem jointRightCandidateAtStep_computable :
    Computable fun a : Program × Nat × Nat => jointRightCandidateAtStep a.1 a.2.1 a.2.2 :=
  jointRightCandidateAtStep_primrec.to_comp

/-- Add an optional newly discovered output to the end of an output list, unless it is already
present. -/
def appendIfNew (xs : List Program) (oy : Option Program) : List Program :=
  match oy with
  | none => xs
  | some y => if y ∈ xs then xs else xs ++ [y]

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

theorem sublist_appendIfNew (xs : List Program) (oy : Option Program) :
    List.Sublist xs (appendIfNew xs oy) := by
  cases oy with
  | none =>
      simp [appendIfNew]
  | some y =>
      by_cases hy : y ∈ xs
      · simp [appendIfNew, hy]
      · simp [appendIfNew, hy]

theorem nodup_appendIfNew {xs : List Program} (hxs : xs.Nodup) (oy : Option Program) :
    (appendIfNew xs oy).Nodup := by
  cases oy with
  | none =>
      simpa [appendIfNew] using hxs
  | some y =>
      by_cases hy : y ∈ xs
      · simpa [appendIfNew, hy] using hxs
      · simpa [appendIfNew, hy, List.concat_eq_append] using hxs.concat hy

theorem mem_appendIfNew_iff {xs : List Program} {oy : Option Program} {y : Program} :
    y ∈ appendIfNew xs oy ↔ y ∈ xs ∨ oy = some y := by
  cases oy with
  | none =>
      simp [appendIfNew]
  | some z =>
      by_cases hz : z ∈ xs
      · rw [appendIfNew, if_pos hz]
        constructor
        · intro hy
          exact Or.inl hy
        · rintro (hy | hEq)
          · exact hy
          · injection hEq with hzy
            simpa [hzy] using hz
      · simpa [appendIfNew, hz, List.mem_append, eq_comm]

/-- Discovery-order list of distinct right outputs found by scanning the first `t` many
joint-right discovery attempts. -/
def jointRightDiscoveredUpToStep (x : Program) (n : Nat) : Nat → List Program
  | 0 => []
  | t + 1 =>
      appendIfNew (jointRightDiscoveredUpToStep x n t) (jointRightCandidateAtStep x n t)

@[simp] theorem jointRightDiscoveredUpToStep_zero (x : Program) (n : Nat) :
    jointRightDiscoveredUpToStep x n 0 = [] := rfl

@[simp] theorem jointRightDiscoveredUpToStep_succ (x : Program) (n t : Nat) :
    jointRightDiscoveredUpToStep x n (t + 1) =
      appendIfNew (jointRightDiscoveredUpToStep x n t) (jointRightCandidateAtStep x n t) := rfl

theorem nodup_jointRightDiscoveredUpToStep (x : Program) (n t : Nat) :
    (jointRightDiscoveredUpToStep x n t).Nodup := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      simpa [jointRightDiscoveredUpToStep_succ] using
        nodup_appendIfNew ih (jointRightCandidateAtStep x n t)

theorem mem_jointRightOutputsUpToLength_of_mem_jointRightDiscoveredUpToStep
    {x y : Program} {n t : Nat}
    (hy : y ∈ jointRightDiscoveredUpToStep x n t) :
    y ∈ jointRightOutputsUpToLength x n := by
  induction t with
  | zero =>
      simp at hy
  | succ t ih =>
      rw [jointRightDiscoveredUpToStep_succ, mem_appendIfNew_iff] at hy
      rcases hy with hy | hy
      · exact ih hy
      · exact mem_jointRightOutputsUpToLength_of_jointComplexity_le
          (jointRightCandidateAtStep_sound hy)

theorem exists_jointRightDiscoveryStep_of_jointComplexity_le {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    ∃ t, y ∈ jointRightDiscoveredUpToStep x n t := by
  rcases jointRightCandidateAtStep_complete (x := x) (y := y) (n := n) hxy with ⟨t, ht⟩
  refine ⟨t + 1, ?_⟩
  rw [jointRightDiscoveredUpToStep_succ, mem_appendIfNew_iff]
  exact Or.inr ht

theorem length_jointRightDiscoveredUpToStep_le (x : Program) (n t : Nat) :
    (jointRightDiscoveredUpToStep x n t).length ≤ (jointRightOutputsUpToLength x n).length := by
  have hsubset :
      (jointRightDiscoveredUpToStep x n t).toFinset ⊆ (jointRightOutputsUpToLength x n).toFinset := by
    intro y hy
    rw [List.mem_toFinset] at hy ⊢
    exact mem_jointRightOutputsUpToLength_of_mem_jointRightDiscoveredUpToStep hy
  have hcard :
      (jointRightDiscoveredUpToStep x n t).toFinset.card ≤
        (jointRightOutputsUpToLength x n).toFinset.card := Finset.card_le_card hsubset
  rwa [List.toFinset_card_of_nodup (nodup_jointRightDiscoveredUpToStep x n t),
    List.toFinset_card_of_nodup (nodup_jointRightOutputsUpToLength x n)] at hcard

private theorem getElem?_appendIfNew_of_getElem? {xs : List Program} {oy : Option Program}
    {i : Nat} {y : Program} (hy : xs[i]? = some y) :
    (appendIfNew xs oy)[i]? = some y := by
  cases oy with
  | none =>
      simpa [appendIfNew] using hy
  | some z =>
      by_cases hz : z ∈ xs
      · simpa [appendIfNew, hz] using hy
      · have hi : i < xs.length := (List.getElem?_eq_some_iff.mp hy).1
        rw [appendIfNew, if_neg hz, List.getElem?_append_left hi]
        exact hy

private theorem jointRightDiscoveredUpToStep_getElem?_mono {x : Program} {n t u i : Nat}
    {y : Program} (htu : t ≤ u)
    (hy : (jointRightDiscoveredUpToStep x n t)[i]? = some y) :
    (jointRightDiscoveredUpToStep x n u)[i]? = some y := by
  induction htu with
  | refl =>
      exact hy
  | @step u htu ih =>
      rw [jointRightDiscoveredUpToStep_succ]
      exact getElem?_appendIfNew_of_getElem? ih

private theorem mem_jointRightDiscoveredUpToStep_mono {x y : Program} {n t u : Nat}
    (htu : t ≤ u)
    (hy : y ∈ jointRightDiscoveredUpToStep x n t) :
    y ∈ jointRightDiscoveredUpToStep x n u := by
  rw [List.mem_iff_getElem?] at hy
  rcases hy with ⟨i, hi⟩
  rw [List.mem_iff_getElem?]
  exact ⟨i, jointRightDiscoveredUpToStep_getElem?_mono htu hi⟩

private theorem exists_jointRightDiscoveryStep_coveringList {x : Program} {n : Nat} :
    ∀ L : List Program,
      (∀ y ∈ L, y ∈ jointRightOutputsUpToLength x n) →
      ∃ t, ∀ y ∈ L, y ∈ jointRightDiscoveredUpToStep x n t
  | [], _ => ⟨0, by simp⟩
  | y :: ys, hL => by
      have hyOut : y ∈ jointRightOutputsUpToLength x n := hL y (by simp)
      have hyComplexity : JointComplexity x y ≤ n := by
        have hz : packedInput x y ∈ prefixOutputsUpToLength [] n :=
          mem_prefixOutputsUpToLength_of_mem_jointRightOutputsUpToLength hyOut
        exact (jointComplexity_le_iff_existsWitness (x := x) (y := y) (n := n)).mpr
          ((mem_prefixOutputsUpToLength_iff_existsWitness
            (x := packedInput x y) (input := ([] : Program)) (n := n)).mp hz)
      obtain ⟨ty, hyDisc⟩ := exists_jointRightDiscoveryStep_of_jointComplexity_le
        hyComplexity
      obtain ⟨tys, hys⟩ := exists_jointRightDiscoveryStep_coveringList ys (by
        intro z hz
        exact hL z (by simp [hz]))
      refine ⟨max ty tys, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact mem_jointRightDiscoveredUpToStep_mono (le_max_left _ _) hyDisc
      · exact mem_jointRightDiscoveredUpToStep_mono (le_max_right _ _) (hys z hz)

private theorem exists_jointRightDiscoveryStep_of_card_le {x : Program} {n k : Nat}
    (hk : k ≤ (jointRightOutputsUpToLength x n).length) :
    ∃ t, k ≤ (jointRightDiscoveredUpToStep x n t).length := by
  let L := (jointRightOutputsUpToLength x n).take k
  obtain ⟨t, hcover⟩ := exists_jointRightDiscoveryStep_coveringList (x := x) (n := n) L (by
    intro y hy
    exact List.mem_of_mem_take hy)
  have hsubset : L.toFinset ⊆ (jointRightDiscoveredUpToStep x n t).toFinset := by
    intro y hy
    rw [List.mem_toFinset] at hy ⊢
    exact hcover y hy
  have hcard :
      L.length ≤ (jointRightDiscoveredUpToStep x n t).length := by
    have hcard' : L.toFinset.card ≤ (jointRightDiscoveredUpToStep x n t).toFinset.card :=
      Finset.card_le_card hsubset
    have hnodupL : L.Nodup := (nodup_jointRightOutputsUpToLength x n).sublist (List.take_sublist _ _)
    rwa [List.toFinset_card_of_nodup hnodupL,
      List.toFinset_card_of_nodup (nodup_jointRightDiscoveredUpToStep x n t)] at hcard'
  refine ⟨t, ?_⟩
  have hlenL : L.length = k := by
    dsimp [L]
    rw [List.length_take, Nat.min_eq_left hk]
  exact hlenL ▸ hcard

private theorem jointRightDiscoveredUpToStep_primrec :
    Primrec fun a : Program × Nat × Nat => jointRightDiscoveredUpToStep a.1 a.2.1 a.2.2 := by
  have hcandArg :
      Primrec fun p : (Program × Nat × Nat) × (Nat × List Program) =>
        (p.1.1, p.1.2.1, p.2.1) := by
    exact Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
  have hstep :
      Primrec₂ fun (a : Program × Nat × Nat) (p : Nat × List Program) =>
        appendIfNew p.2 (jointRightCandidateAtStep a.1 a.2.1 p.1) := by
    exact appendIfNew_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (jointRightCandidateAtStep_primrec.comp hcandArg)
  refine (Primrec.nat_rec' (Primrec.snd.comp Primrec.snd)
    (Primrec.const ([] : List Program)) hstep).of_eq ?_
  intro a
  cases a with
  | mk x ni =>
      cases ni with
      | mk n t =>
          induction t with
          | zero =>
              rfl
          | succ t ih =>
              simp [jointRightDiscoveredUpToStep, ih]

private theorem jointRightDiscoveredUpToStep_computable :
    Computable fun a : Program × Nat × Nat => jointRightDiscoveredUpToStep a.1 a.2.1 a.2.2 :=
  jointRightDiscoveredUpToStep_primrec.to_comp

/-- Search step for the concrete bounded right-output enumerator. -/
private def jointRightSearchStep (a : Program × Nat × Nat) (t : Nat) : Option Program :=
  (jointRightDiscoveredUpToStep a.1 a.2.1 t)[a.2.2]?

private theorem jointRightSearchStep_primrec : Primrec₂ jointRightSearchStep := by
  simpa [jointRightSearchStep] using
    (Primrec.list_getElem?.comp
      (jointRightDiscoveredUpToStep_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

private theorem jointRightSearchStep_computable : Computable₂ jointRightSearchStep :=
  jointRightSearchStep_primrec.to_comp

private def jointRightArgsOfNat (inputNat : Nat) : Program × Nat × Nat :=
  let input := BitString.ofNatExact inputNat
  let w := unpackInput input
  let ni := BitString.decodeExactPairPayload w.2
  (w.1, BitString.toNatExact ni.1, BitString.toNatExact ni.2)

private theorem jointRightArgsOfNat_computable : Computable jointRightArgsOfNat := by
  have hinput : Computable fun inputNat : Nat => BitString.ofNatExact inputNat :=
    BitString.ofNatExact_computable
  have hpair :
      Computable fun inputNat : Nat =>
        unpackInput (BitString.ofNatExact inputNat) :=
    unpackInput_computable.comp hinput
  have hdecoded :
      Computable fun inputNat : Nat =>
        BitString.decodeExactPairPayload (unpackInput (BitString.ofNatExact inputNat)).2 :=
    BitString.decodeExactPairPayload_computable.comp (Computable.snd.comp hpair)
  refine Computable.pair (Computable.fst.comp hpair) ?_
  exact Computable.pair
    (BitString.toNatExact_computable.comp (Computable.fst.comp hdecoded))
    (BitString.toNatExact_computable.comp (Computable.snd.comp hdecoded))

private def jointRightSearchStepNat (inputNat t : Nat) : Option Nat :=
  (jointRightSearchStep (jointRightArgsOfNat inputNat) t).map BitString.toNatExact

private theorem jointRightSearchStepNat_computable : Computable₂ jointRightSearchStepNat := by
  exact Computable.option_map
    (jointRightSearchStep_computable.comp
      (jointRightArgsOfNat_computable.comp Computable.fst)
      Computable.snd)
    ((BitString.toNatExact_computable.comp Computable.snd).to₂)

theorem jointComplexity_le_of_mem_jointRightOutputsUpToLength {x y : Program} {n : Nat}
    (hy : y ∈ jointRightOutputsUpToLength x n) :
    JointComplexity x y ≤ n := by
  have hz : packedInput x y ∈ prefixOutputsUpToLength [] n :=
    mem_prefixOutputsUpToLength_of_mem_jointRightOutputsUpToLength hy
  exact (jointComplexity_le_iff_existsWitness (x := x) (y := y) (n := n)).mpr
    ((mem_prefixOutputsUpToLength_iff_existsWitness
      (x := packedInput x y) (input := ([] : Program)) (n := n)).mp hz)

theorem exists_jointRightDiscoveryIndex_of_mem {x y : Program} {n : Nat}
    (hy : y ∈ jointRightOutputsUpToLength x n) :
    ∃ i < (jointRightOutputsUpToLength x n).length, ∃ t,
      (jointRightDiscoveredUpToStep x n t)[i]? = some y := by
  obtain ⟨t, ht⟩ := exists_jointRightDiscoveryStep_of_jointComplexity_le
    (jointComplexity_le_of_mem_jointRightOutputsUpToLength hy)
  rw [List.mem_iff_getElem?] at ht
  rcases ht with ⟨i, hget⟩
  have hiDisc : i < (jointRightDiscoveredUpToStep x n t).length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have hi : i < (jointRightOutputsUpToLength x n).length := by
    exact lt_of_lt_of_le hiDisc (length_jointRightDiscoveredUpToStep_le x n t)
  exact ⟨i, hi, t, hget⟩

theorem exists_jointRightIndex_of_jointComplexity_le {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    ∃ i < 2 ^ (n + 1) - 1, (jointRightOutputsUpToLength x n)[i]? = some y := by
  have hmem := mem_jointRightOutputsUpToLength_of_jointComplexity_le (x := x) (y := y) hxy
  rw [List.mem_iff_getElem?] at hmem
  rcases hmem with ⟨i, hi⟩
  refine ⟨i, ?_, hi⟩
  have hiLen : i < (jointRightOutputsUpToLength x n).length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.not_lt.mp hge)] at hi
    simp at hi
  exact lt_of_lt_of_le hiLen (length_jointRightOutputsUpToLength_le x n)

/-- For fixed `n` and threshold `2^m`, the left components that have at least `2^m` distinct
right partners among joint descriptions of complexity at most `n`. -/
noncomputable def jointLeftOutputsWithAtLeastCount (n m : Nat) : Finset Program :=
  ((prefixOutputsUpToLength [] n).filterMap fun z =>
    let x := (unpackInput z).1
    if 2 ^ m ≤ (jointRightOutputsUpToLength x n).length then some x else none).toFinset

theorem mem_jointLeftOutputsWithAtLeastCount_of_jointComplexity_le {x y : Program} {n m : Nat}
    (hxy : JointComplexity x y ≤ n)
    (hcount : 2 ^ m ≤ (jointRightOutputsUpToLength x n).length) :
    x ∈ jointLeftOutputsWithAtLeastCount n m := by
  unfold jointLeftOutputsWithAtLeastCount
  rw [List.mem_toFinset, List.mem_filterMap]
  refine ⟨packedInput x y, mem_prefixOutputsUpToLength_of_jointComplexity_le hxy, ?_⟩
  simp [hcount]

theorem pow_le_length_jointRightOutputsUpToLength_of_mem_jointLeftOutputsWithAtLeastCount
    {x : Program} {n m : Nat}
    (hx : x ∈ jointLeftOutputsWithAtLeastCount n m) :
    2 ^ m ≤ (jointRightOutputsUpToLength x n).length := by
  unfold jointLeftOutputsWithAtLeastCount at hx
  rw [List.mem_toFinset, List.mem_filterMap] at hx
  rcases hx with ⟨z, _, hz⟩
  dsimp at hz
  split_ifs at hz with hcount
  have hx' : (unpackInput z).1 = x := by
    simpa using hz
  simpa [hx'] using hcount

/-- First `2^m` right partners of `x` in the bounded joint-output family, as a finset. -/
noncomputable def firstJointRightOutputsFinset (x : Program) (n m : Nat) : Finset Program :=
  ((jointRightOutputsUpToLength x n).take (2 ^ m)).toFinset

theorem card_firstJointRightOutputsFinset {x : Program} {n m : Nat}
    (hx : 2 ^ m ≤ (jointRightOutputsUpToLength x n).length) :
    (firstJointRightOutputsFinset x n m).card = 2 ^ m := by
  unfold firstJointRightOutputsFinset
  have hnodup :
      ((jointRightOutputsUpToLength x n).take (2 ^ m)).Nodup := by
    exact (nodup_jointRightOutputsUpToLength x n).sublist (List.take_sublist _ _)
  rw [List.toFinset_card_of_nodup hnodup, List.length_take, Nat.min_eq_left hx]

theorem packedInput_right_injective (x : Program) : Function.Injective (packedInput x) := by
  intro y y' h
  have hpair : unpackInput (packedInput x y) = unpackInput (packedInput x y') := congrArg unpackInput h
  simpa using congrArg Prod.snd hpair

theorem packedInput_sigma_injective :
    Function.Injective (fun a : Σ _ : Program, Program => packedInput a.1 a.2) := by
  intro a b h
  cases a with
  | mk x y =>
      cases b with
      | mk x' y' =>
          have hpair : (x, y) = (x', y') := by
            simpa using congrArg unpackInput h
          cases hpair
          rfl

theorem card_jointLeftOutputsWithAtLeastCount_mul_pow_le (n m : Nat) :
    (jointLeftOutputsWithAtLeastCount n m).card * 2 ^ m ≤ 2 ^ (n + 1) - 1 := by
  let s : Finset Program := jointLeftOutputsWithAtLeastCount n m
  let t : Program → Finset Program := fun x => firstJointRightOutputsFinset x n m
  have hsigma :
      (s.sigma t).card = s.card * 2 ^ m := by
    rw [Finset.card_sigma]
    exact Finset.sum_const_nat (by
      intro x hx
      exact card_firstJointRightOutputsFinset
        (pow_le_length_jointRightOutputsUpToLength_of_mem_jointLeftOutputsWithAtLeastCount
          (n := n) (m := m) hx))
  have hmap :
      Set.MapsTo (fun a : Σ _ : Program, Program => packedInput a.1 a.2)
        (s.sigma t) ((prefixOutputsUpToLength [] n).toFinset) := by
    intro a ha
    rcases Finset.mem_sigma.mp ha with ⟨hx, hy⟩
    have hytake : a.2 ∈ (jointRightOutputsUpToLength a.1 n).take (2 ^ m) := by
      simpa [t, firstJointRightOutputsFinset] using hy
    exact List.mem_toFinset.mpr <|
      mem_prefixOutputsUpToLength_of_mem_jointRightOutputsUpToLength
        (List.mem_of_mem_take hytake)
  have hinj :
      Set.InjOn (fun a : Σ _ : Program, Program => packedInput a.1 a.2) (s.sigma t) := by
    exact packedInput_sigma_injective.injOn
  have hcard :
      (s.sigma t).card ≤ ((prefixOutputsUpToLength [] n).toFinset).card := by
    exact Finset.card_le_card_of_injOn _ hmap hinj
  have hcod :
      ((prefixOutputsUpToLength [] n).toFinset).card ≤ 2 ^ (n + 1) - 1 := by
    rw [List.toFinset_card_of_nodup (nodup_prefixOutputsUpToLength [] n)]
    exact length_prefixOutputsUpToLength_le [] n
  calc
    (jointLeftOutputsWithAtLeastCount n m).card * 2 ^ m = (s.sigma t).card := by
      simpa [s, t] using hsigma.symm
    _ ≤ ((prefixOutputsUpToLength [] n).toFinset).card := hcard
    _ ≤ 2 ^ (n + 1) - 1 := hcod

theorem card_jointLeftOutputsWithAtLeastCount_le (n m : Nat) :
    (jointLeftOutputsWithAtLeastCount n m).card ≤ 2 ^ (n + 1 - m) - 1 := by
  have hmul := card_jointLeftOutputsWithAtLeastCount_mul_pow_le n m
  have hlt :
      (jointLeftOutputsWithAtLeastCount n m).card * 2 ^ m < 2 ^ (n + 1) := by
    have hpowpos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by decide : 0 < 2)
    exact lt_of_le_of_lt hmul (Nat.sub_lt hpowpos (by decide))
  by_cases hm : m ≤ n + 1
  · have hpow :
        2 ^ (n + 1) = (2 ^ (n + 1 - m)) * (2 ^ m) := by
      have hsum : n + 1 = (n + 1 - m) + m := by omega
      have hpow0 : 2 ^ ((n + 1 - m) + m) = (2 ^ (n + 1 - m)) * (2 ^ m) :=
        Nat.pow_add 2 (n + 1 - m) m
      calc
        2 ^ (n + 1) = 2 ^ ((n + 1 - m) + m) := by exact congrArg (fun t => 2 ^ t) hsum
        _ = (2 ^ (n + 1 - m)) * (2 ^ m) := hpow0
    have hlt' :
        (jointLeftOutputsWithAtLeastCount n m).card < 2 ^ (n + 1 - m) := by
      by_contra hge
      have hge' : 2 ^ (n + 1 - m) ≤ (jointLeftOutputsWithAtLeastCount n m).card := by
        exact Nat.le_of_not_gt hge
      have hcontra :
          2 ^ (n + 1) ≤ (jointLeftOutputsWithAtLeastCount n m).card * 2 ^ m := by
        calc
          2 ^ (n + 1) = (2 ^ (n + 1 - m)) * (2 ^ m) := hpow
          _ ≤ (jointLeftOutputsWithAtLeastCount n m).card * 2 ^ m := by
            exact Nat.mul_le_mul_right _ hge'
      exact (not_le_of_gt hlt) hcontra
    exact Nat.le_pred_of_lt hlt'
  · have hm' : n + 1 < m := Nat.lt_of_not_ge hm
    have hzero : (jointLeftOutputsWithAtLeastCount n m).card = 0 := by
      by_contra hpos
      have hcardpos : 1 ≤ (jointLeftOutputsWithAtLeastCount n m).card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpos)
      have hpow_le :
          2 ^ m ≤ (jointLeftOutputsWithAtLeastCount n m).card * 2 ^ m := by
        calc
          2 ^ m = 1 * 2 ^ m := by simp
          _ ≤ (jointLeftOutputsWithAtLeastCount n m).card * 2 ^ m := by
            exact Nat.mul_le_mul_right _ hcardpos
      have hpow_ge : 2 ^ (n + 1) ≤ 2 ^ m := by
        exact Nat.pow_le_pow_right (by decide) hm'.le
      exact (not_le_of_gt hlt) (le_trans hpow_ge hpow_le)
    rw [hzero]
    have hsub : n + 1 - m = 0 := Nat.sub_eq_zero_of_le hm'.le
    simp [hsub]

/-- Canonical list view of the heavy-left family. -/
noncomputable def jointLeftOutputsWithAtLeastCountList (n m : Nat) : List Program :=
  (jointLeftOutputsWithAtLeastCount n m).toList

theorem exists_jointLeftIndex_of_mem {x : Program} {n m : Nat}
    (hx : x ∈ jointLeftOutputsWithAtLeastCount n m) :
    ∃ i < (jointLeftOutputsWithAtLeastCount n m).card,
      (jointLeftOutputsWithAtLeastCountList n m)[i]? = some x := by
  have hxList : x ∈ jointLeftOutputsWithAtLeastCountList n m := by
    simpa [jointLeftOutputsWithAtLeastCountList] using (Finset.mem_toList.mpr hx)
  rw [List.mem_iff_getElem?] at hxList
  rcases hxList with ⟨i, hget⟩
  have hi : i < (jointLeftOutputsWithAtLeastCountList n m).length := by
    exact (List.getElem?_eq_some_iff.mp hget).1
  exact ⟨i, by simpa [jointLeftOutputsWithAtLeastCountList] using hi, hget⟩

/-- Discovery attempt for the heavy-left family: scan one packed joint output candidate, then test
whether its left component has already accumulated at least `2^m` distinct right partners. -/
def jointLeftCandidateAtStep (n m q : Nat) : Option Program :=
  (jointPackedCandidateAtStep n q.unpair.1).bind fun z =>
    let x := (unpackInput z).1
    if 2 ^ m ≤ (jointRightDiscoveredUpToStep x n q.unpair.2).length then some x else none

theorem jointLeftCandidateAtStep_sound {n m q : Nat} {x : Program}
    (h : jointLeftCandidateAtStep n m q = some x) :
    x ∈ jointLeftOutputsWithAtLeastCount n m := by
  unfold jointLeftCandidateAtStep at h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨z, hz, hx⟩
  have hxy : JointComplexity (unpackInput z).1 (unpackInput z).2 ≤ n :=
    jointPackedCandidateAtStep_sound hz
  have hcount :
      2 ^ m ≤ (jointRightDiscoveredUpToStep (unpackInput z).1 n q.unpair.2).length := by
    by_cases hc : 2 ^ m ≤ (jointRightDiscoveredUpToStep (unpackInput z).1 n q.unpair.2).length
    · simpa [hc] using hx
    · simp [hc] at hx
  have hxEq : (unpackInput z).1 = x := by
    by_cases hc : 2 ^ m ≤ (jointRightDiscoveredUpToStep (unpackInput z).1 n q.unpair.2).length
    · simpa [hc] using hx
    · simp [hc] at hx
  have hcountFull :
      2 ^ m ≤ (jointRightOutputsUpToLength (unpackInput z).1 n).length := by
    exact le_trans hcount (length_jointRightDiscoveredUpToStep_le (unpackInput z).1 n q.unpair.2)
  have hxMem :
      (unpackInput z).1 ∈ jointLeftOutputsWithAtLeastCount n m :=
    mem_jointLeftOutputsWithAtLeastCount_of_jointComplexity_le hxy hcountFull
  simpa [hxEq] using hxMem

theorem jointLeftCandidateAtStep_complete {x : Program} {n m : Nat}
    (hx : x ∈ jointLeftOutputsWithAtLeastCount n m) :
    ∃ q, jointLeftCandidateAtStep n m q = some x := by
  have hpow :
      2 ^ m ≤ (jointRightOutputsUpToLength x n).length :=
    pow_le_length_jointRightOutputsUpToLength_of_mem_jointLeftOutputsWithAtLeastCount hx
  have hpos : 0 < (jointRightOutputsUpToLength x n).length := by
    exact lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 2)) hpow
  let y : Program := (jointRightOutputsUpToLength x n)[0]'hpos
  have hy : y ∈ jointRightOutputsUpToLength x n := by
    dsimp [y]
    rw [List.mem_iff_getElem]
    exact ⟨0, hpos, rfl⟩
  have hxy : JointComplexity x y ≤ n :=
    jointComplexity_le_of_mem_jointRightOutputsUpToLength hy
  obtain ⟨t, ht⟩ := jointPackedCandidateAtStep_complete hxy
  obtain ⟨s, hs⟩ := exists_jointRightDiscoveryStep_of_card_le (x := x) (n := n) hpow
  refine ⟨Nat.pair t s, ?_⟩
  simp [jointLeftCandidateAtStep, Nat.unpair_pair, ht, hs, unpackInput_packedInput]

/-- Discovery-order list of distinct heavy-left outputs found by scanning the first `r` many
heavy-left discovery attempts. -/
def jointLeftDiscoveredUpToStep (n m : Nat) : Nat → List Program
  | 0 => []
  | r + 1 =>
      appendIfNew (jointLeftDiscoveredUpToStep n m r) (jointLeftCandidateAtStep n m r)

@[simp] theorem jointLeftDiscoveredUpToStep_zero (n m : Nat) :
    jointLeftDiscoveredUpToStep n m 0 = [] := rfl

@[simp] theorem jointLeftDiscoveredUpToStep_succ (n m r : Nat) :
    jointLeftDiscoveredUpToStep n m (r + 1) =
      appendIfNew (jointLeftDiscoveredUpToStep n m r) (jointLeftCandidateAtStep n m r) := rfl

theorem nodup_jointLeftDiscoveredUpToStep (n m r : Nat) :
    (jointLeftDiscoveredUpToStep n m r).Nodup := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      simpa [jointLeftDiscoveredUpToStep_succ] using
        nodup_appendIfNew ih (jointLeftCandidateAtStep n m r)

theorem mem_jointLeftOutputsWithAtLeastCount_of_mem_jointLeftDiscoveredUpToStep
    {x : Program} {n m r : Nat}
    (hx : x ∈ jointLeftDiscoveredUpToStep n m r) :
    x ∈ jointLeftOutputsWithAtLeastCount n m := by
  induction r with
  | zero =>
      simp at hx
  | succ r ih =>
      rw [jointLeftDiscoveredUpToStep_succ, mem_appendIfNew_iff] at hx
      rcases hx with hx | hx
      · exact ih hx
      · exact jointLeftCandidateAtStep_sound hx

theorem exists_jointLeftDiscoveryStep_of_mem {x : Program} {n m : Nat}
    (hx : x ∈ jointLeftOutputsWithAtLeastCount n m) :
    ∃ r, x ∈ jointLeftDiscoveredUpToStep n m r := by
  obtain ⟨q, hq⟩ := jointLeftCandidateAtStep_complete hx
  refine ⟨q + 1, ?_⟩
  rw [jointLeftDiscoveredUpToStep_succ, mem_appendIfNew_iff]
  exact Or.inr hq

theorem length_jointLeftDiscoveredUpToStep_le (n m r : Nat) :
    (jointLeftDiscoveredUpToStep n m r).length ≤ (jointLeftOutputsWithAtLeastCount n m).card := by
  have hsubset :
      (jointLeftDiscoveredUpToStep n m r).toFinset ⊆ jointLeftOutputsWithAtLeastCount n m := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact mem_jointLeftOutputsWithAtLeastCount_of_mem_jointLeftDiscoveredUpToStep hx
  have hcard :
      (jointLeftDiscoveredUpToStep n m r).toFinset.card ≤
        (jointLeftOutputsWithAtLeastCount n m).card := Finset.card_le_card hsubset
  rwa [List.toFinset_card_of_nodup (nodup_jointLeftDiscoveredUpToStep n m r)] at hcard

theorem exists_jointLeftDiscoveryIndex_of_mem {x : Program} {n m : Nat}
    (hx : x ∈ jointLeftOutputsWithAtLeastCount n m) :
    ∃ i < (jointLeftOutputsWithAtLeastCount n m).card, ∃ r,
      (jointLeftDiscoveredUpToStep n m r)[i]? = some x := by
  obtain ⟨r, hr⟩ := exists_jointLeftDiscoveryStep_of_mem hx
  rw [List.mem_iff_getElem?] at hr
  rcases hr with ⟨i, hget⟩
  have hiDisc : i < (jointLeftDiscoveredUpToStep n m r).length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have hi : i < (jointLeftOutputsWithAtLeastCount n m).card := by
    exact lt_of_lt_of_le hiDisc (length_jointLeftDiscoveredUpToStep_le n m r)
  exact ⟨i, hi, r, hget⟩

/-- Payload encoding used to specify a heavy-left candidate via `(n, m, i)`. -/
def jointLeftCountPayload (n m i : Nat) : Program :=
  BitString.exactPairPayload (BitString.ofNatExact n)
    (BitString.exactPairPayload (BitString.ofNatExact m) (BitString.ofNatExact i))

/-- Specification of an interpreter enumerating the heavy-left family at threshold `2^m`. -/
def IsJointLeftCountEnumerator (u : Program) : Prop :=
  ∀ n m : Nat, ∀ x : Program,
    x ∈ jointLeftOutputsWithAtLeastCount n m →
      ∃ i < (jointLeftOutputsWithAtLeastCount n m).card,
        runs u (packedInput [] (jointLeftCountPayload n m i)) x

private theorem jointLeftCandidateAtStep_primrec :
    Primrec fun a : Nat × Nat × Nat => jointLeftCandidateAtStep a.1 a.2.1 a.2.2 := by
  have hqLeft : Primrec fun a : Nat × Nat × Nat => a.2.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hqRight : Primrec fun a : Nat × Nat × Nat => a.2.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hpacked :
      Primrec fun a : Nat × Nat × Nat =>
        jointPackedCandidateAtStep a.1 a.2.2.unpair.1 :=
    jointPackedCandidateAtStep_primrec.comp (Primrec.pair Primrec.fst hqLeft)
  have hpow2 : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hpow :
      Primrec fun p : (Nat × Nat × Nat) × Program => 2 ^ p.1.2.1 :=
    hpow2.comp (Primrec.const 2) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hdiscArg :
      Primrec fun p : (Nat × Nat × Nat) × Program =>
        ((unpackInput p.2).1, p.1.1, p.1.2.2.unpair.2) := by
    exact Primrec.pair
      (Primrec.fst.comp (unpackInput_primrec.comp Primrec.snd))
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (hqRight.comp Primrec.fst))
  have hdiscLen :
      Primrec fun p : (Nat × Nat × Nat) × Program =>
        (jointRightDiscoveredUpToStep (unpackInput p.2).1 p.1.1 p.1.2.2.unpair.2).length := by
    exact Primrec.list_length.comp (jointRightDiscoveredUpToStep_primrec.comp hdiscArg)
  have hpred :
      PrimrecPred fun p : (Nat × Nat × Nat) × Program =>
        2 ^ p.1.2.1 ≤
          (jointRightDiscoveredUpToStep (unpackInput p.2).1 p.1.1 p.1.2.2.unpair.2).length := by
    exact PrimrecRel.comp Primrec.nat_le hpow hdiscLen
  have hsome :
      Primrec fun p : (Nat × Nat × Nat) × Program =>
        some ((unpackInput p.2).1) :=
    Primrec.option_some.comp (Primrec.fst.comp (unpackInput_primrec.comp Primrec.snd))
  have hselect :
      Primrec₂ fun (a : Nat × Nat × Nat) (z : Program) =>
        if 2 ^ a.2.1 ≤ (jointRightDiscoveredUpToStep (unpackInput z).1 a.1 a.2.2.unpair.2).length
        then some (unpackInput z).1
        else none := by
    exact (Primrec.ite hpred hsome (Primrec.const (Option.none : Option Program))).to₂
  exact (Primrec.option_bind hpacked hselect).of_eq fun a => by
    cases a with
    | mk n mq =>
        cases mq with
        | mk m q =>
            simp [jointLeftCandidateAtStep]

private theorem jointLeftCandidateAtStep_computable :
    Computable fun a : Nat × Nat × Nat => jointLeftCandidateAtStep a.1 a.2.1 a.2.2 :=
  jointLeftCandidateAtStep_primrec.to_comp

private theorem jointLeftDiscoveredUpToStep_primrec :
    Primrec fun a : Nat × Nat × Nat => jointLeftDiscoveredUpToStep a.1 a.2.1 a.2.2 := by
  have hcandArg :
      Primrec fun p : (Nat × Nat × Nat) × (Nat × List Program) =>
        (p.1.1, p.1.2.1, p.2.1) := by
    exact Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
  have hstep :
      Primrec₂ fun (a : Nat × Nat × Nat) (p : Nat × List Program) =>
        appendIfNew p.2 (jointLeftCandidateAtStep a.1 a.2.1 p.1) := by
    exact appendIfNew_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (jointLeftCandidateAtStep_primrec.comp hcandArg)
  refine (Primrec.nat_rec' (Primrec.snd.comp Primrec.snd)
    (Primrec.const ([] : List Program)) hstep).of_eq ?_
  intro a
  cases a with
  | mk n mq =>
      cases mq with
      | mk m r =>
          induction r with
          | zero =>
              rfl
          | succ r ih =>
              simp [jointLeftDiscoveredUpToStep, ih]

private theorem jointLeftDiscoveredUpToStep_computable :
    Computable fun a : Nat × Nat × Nat => jointLeftDiscoveredUpToStep a.1 a.2.1 a.2.2 :=
  jointLeftDiscoveredUpToStep_primrec.to_comp

private theorem jointLeftDiscoveredUpToStep_getElem?_mono {n m r s i : Nat} {x : Program}
    (hrs : r ≤ s)
    (hx : (jointLeftDiscoveredUpToStep n m r)[i]? = some x) :
    (jointLeftDiscoveredUpToStep n m s)[i]? = some x := by
  induction hrs with
  | refl =>
      exact hx
  | @step s hrs ih =>
      rw [jointLeftDiscoveredUpToStep_succ]
      exact getElem?_appendIfNew_of_getElem? ih

/-- Search step for the concrete heavy-left enumerator. -/
private def jointLeftSearchStep (a : Nat × Nat × Nat) (r : Nat) : Option Program :=
  (jointLeftDiscoveredUpToStep a.1 a.2.1 r)[a.2.2]?

private theorem jointLeftSearchStep_primrec : Primrec₂ jointLeftSearchStep := by
  simpa [jointLeftSearchStep] using
    (Primrec.list_getElem?.comp
      (jointLeftDiscoveredUpToStep_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

private theorem jointLeftSearchStep_computable : Computable₂ jointLeftSearchStep :=
  jointLeftSearchStep_primrec.to_comp

private def jointLeftArgsOfNat (inputNat : Nat) : Nat × Nat × Nat :=
  let payload := (unpackInput (BitString.ofNatExact inputNat)).2
  let ni := BitString.decodeExactPairPayload payload
  let mi := BitString.decodeExactPairPayload ni.2
  (BitString.toNatExact ni.1, BitString.toNatExact mi.1, BitString.toNatExact mi.2)

private theorem jointLeftArgsOfNat_computable : Computable jointLeftArgsOfNat := by
  have hpayload :
      Computable fun inputNat : Nat =>
        (unpackInput (BitString.ofNatExact inputNat)).2 := by
    exact Computable.snd.comp (unpackInput_computable.comp BitString.ofNatExact_computable)
  have houter :
      Computable fun inputNat : Nat =>
        BitString.decodeExactPairPayload ((unpackInput (BitString.ofNatExact inputNat)).2) :=
    BitString.decodeExactPairPayload_computable.comp hpayload
  have hinner :
      Computable fun inputNat : Nat =>
        BitString.decodeExactPairPayload
          (BitString.decodeExactPairPayload ((unpackInput (BitString.ofNatExact inputNat)).2)).2 :=
    BitString.decodeExactPairPayload_computable.comp (Computable.snd.comp houter)
  refine Computable.pair
    (BitString.toNatExact_computable.comp (Computable.fst.comp houter)) ?_
  exact Computable.pair
    (BitString.toNatExact_computable.comp (Computable.fst.comp hinner))
    (BitString.toNatExact_computable.comp (Computable.snd.comp hinner))

private def jointLeftSearchStepNat (inputNat r : Nat) : Option Nat :=
  (jointLeftSearchStep (jointLeftArgsOfNat inputNat) r).map BitString.toNatExact

private theorem jointLeftSearchStepNat_computable : Computable₂ jointLeftSearchStepNat := by
  exact Computable.option_map
    (jointLeftSearchStep_computable.comp
      (jointLeftArgsOfNat_computable.comp Computable.fst)
      Computable.snd)
    ((BitString.toNatExact_computable.comp Computable.snd).to₂)

private theorem jointLeftEnumeratorNat_partrec :
    Nat.Partrec fun inputNat => Nat.rfindOpt (jointLeftSearchStepNat inputNat) := by
  exact Partrec.nat_iff.1 (Partrec.rfindOpt jointLeftSearchStepNat_computable)

private theorem exists_jointLeftEnumeratorCode :
    ∃ c : Nat.Partrec.Code,
      ∀ inputNat : Nat,
        Nat.Partrec.Code.eval c inputNat = Nat.rfindOpt (jointLeftSearchStepNat inputNat) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 jointLeftEnumeratorNat_partrec
  exact ⟨c, fun inputNat => by simpa using congrFun hc inputNat⟩

/-- A fixed program enumerating the heavy-left family used in the lower-chain proof. -/
noncomputable def jointLeftCountEnumeratorCode : Nat.Partrec.Code :=
  Classical.choose exists_jointLeftEnumeratorCode

theorem eval_jointLeftCountEnumeratorCode (inputNat : Nat) :
    Nat.Partrec.Code.eval jointLeftCountEnumeratorCode inputNat =
      Nat.rfindOpt (jointLeftSearchStepNat inputNat) :=
  Classical.choose_spec exists_jointLeftEnumeratorCode inputNat

/-- Concrete program implementing the heavy-left enumerator. -/
noncomputable def jointLeftCountEnumerator : Program :=
  UniversalMachine.codeToProgram jointLeftCountEnumeratorCode

@[simp] private theorem jointLeftArgsOfNat_packedInput (n m i : Nat) :
    jointLeftArgsOfNat (BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i))) = (n, m, i) := by
  have hunpack :
      unpackInput (BitString.ofNatExact (BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i)))) =
        (([] : Program), jointLeftCountPayload n m i) := by
    rw [BitString.ofNatExact_toNatExact]
    exact unpackInput_packedInput [] (jointLeftCountPayload n m i)
  have hpayload :
      (unpackInput (BitString.ofNatExact (BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i))))).2 =
        jointLeftCountPayload n m i :=
    congrArg Prod.snd hunpack
  rw [Prod.mk.injEq]
  constructor
  · calc
      BitString.toNatExact
          (BitString.decodeExactPairPayload
            (unpackInput
              (BitString.ofNatExact (BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i))))).2).1 =
          BitString.toNatExact (BitString.ofNatExact n) := by
            rw [congrArg Prod.snd hunpack, jointLeftCountPayload, BitString.decodeExactPairPayload_exactPairPayload]
      _ = n := BitString.toNatExact_ofNatExact n
  · rw [Prod.mk.injEq]
    constructor
    · calc
        BitString.toNatExact
            (BitString.decodeExactPairPayload
              (BitString.decodeExactPairPayload
                (unpackInput
                  (BitString.ofNatExact
                    (BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i))))).2).2).1 =
            BitString.toNatExact (BitString.ofNatExact m) := by
              rw [hpayload, jointLeftCountPayload,
                BitString.decodeExactPairPayload_exactPairPayload,
                BitString.decodeExactPairPayload_exactPairPayload]
        _ = m := BitString.toNatExact_ofNatExact m
    · calc
        BitString.toNatExact
            (BitString.decodeExactPairPayload
              (BitString.decodeExactPairPayload
                (unpackInput
                  (BitString.ofNatExact
                    (BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i))))).2).2).2 =
            BitString.toNatExact (BitString.ofNatExact i) := by
              rw [hpayload, jointLeftCountPayload,
                BitString.decodeExactPairPayload_exactPairPayload,
                BitString.decodeExactPairPayload_exactPairPayload]
        _ = i := BitString.toNatExact_ofNatExact i

@[simp] private theorem jointLeftSearchStepNat_packedInput (n m i r : Nat) :
    jointLeftSearchStepNat (BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i))) r =
      ((jointLeftDiscoveredUpToStep n m r)[i]?).map BitString.toNatExact := by
  rw [jointLeftSearchStepNat, jointLeftArgsOfNat_packedInput]
  simp [jointLeftSearchStep]

theorem jointLeftCountEnumerator_isJointLeftCountEnumerator :
    IsJointLeftCountEnumerator jointLeftCountEnumerator := by
  intro n m x hx
  obtain ⟨i, hi, r, hr⟩ := exists_jointLeftDiscoveryIndex_of_mem hx
  refine ⟨i, hi, ?_⟩
  let inputNat := BitString.toNatExact (packedInput [] (jointLeftCountPayload n m i))
  have hmono :
      ∀ {a r s}, r ≤ s →
        a ∈ jointLeftSearchStepNat inputNat r →
        a ∈ jointLeftSearchStepNat inputNat s := by
    intro a r s hrs ha
    rw [jointLeftSearchStepNat_packedInput] at ha ⊢
    rw [Option.mem_def] at ha ⊢
    rcases hstep : (jointLeftDiscoveredUpToStep n m r)[i]? with _ | x'
    · simp [hstep] at ha
    · simp [hstep] at ha
      subst a
      have hstep' : (jointLeftDiscoveredUpToStep n m s)[i]? = some x' :=
        jointLeftDiscoveredUpToStep_getElem?_mono hrs hstep
      simp [hstep']
  have hstepNat : BitString.toNatExact x ∈ jointLeftSearchStepNat inputNat r := by
    rw [jointLeftSearchStepNat_packedInput]
    simpa [Option.mem_def, hr]
  have hrfind : BitString.toNatExact x ∈ Nat.rfindOpt (jointLeftSearchStepNat inputNat) := by
    exact (Nat.rfindOpt_mono hmono).2 ⟨r, hstepNat⟩
  rw [jointLeftCountEnumerator, UniversalMachine.runs_codeToProgram_iff]
  have hEval :
      Nat.Partrec.Code.eval jointLeftCountEnumeratorCode inputNat =
        Part.some (BitString.toNatExact x) := by
    calc
      Nat.Partrec.Code.eval jointLeftCountEnumeratorCode inputNat =
          Nat.rfindOpt (jointLeftSearchStepNat inputNat) :=
            eval_jointLeftCountEnumeratorCode inputNat
      _ = Part.some (BitString.toNatExact x) := Part.eq_some_iff.2 hrfind
  change Nat.Partrec.Code.eval jointLeftCountEnumeratorCode inputNat = Part.some (BitString.toNatExact x)
  exact hEval

private theorem blen_ofNat_succ_le_logPenalty_add_two (n : Nat) :
    BitString.blen (BitString.ofNat (n + 1)) ≤ logPenalty n + 2 := by
  have hlt :
      n + 1 < 2 ^ (Nat.size n + 1) := by
    have hle : n + 1 ≤ 2 ^ Nat.size n := Nat.succ_le_of_lt (Nat.lt_size_self n)
    exact lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
  have hsize : Nat.size (n + 1) ≤ Nat.size n + 1 := (Nat.size_le).2 hlt
  calc
    BitString.blen (BitString.ofNat (n + 1)) = Nat.size (n + 1) := BitString.blen_ofNat_eq_size _
    _ ≤ Nat.size n + 1 := hsize
    _ = BitString.blen (BitString.ofNat n) + 1 := by rw [BitString.blen_ofNat_eq_size]
    _ ≤ logPenalty n + 2 := by
      have hlog := blen_ofNat_le_logPenalty_succ n
      omega

private theorem blen_ofNatExact_le_logPenalty_add_two_of_le_succ {m n : Nat}
    (hm : m ≤ n + 1) :
    BitString.blen (BitString.ofNatExact m) ≤ logPenalty n + 2 := by
  calc
    BitString.blen (BitString.ofNatExact m) ≤ BitString.blen (BitString.ofNat m) :=
      BitString.blen_ofNatExact_le_ofNat m
    _ ≤ BitString.blen (BitString.ofNat (n + 1)) := BitString.blen_ofNat_mono hm
    _ ≤ logPenalty n + 2 := blen_ofNat_succ_le_logPenalty_add_two n

private theorem blen_jointLeftCountPayload_le_of_index_lt {n m i : Nat}
    (hm : m ≤ n + 1)
    (hi : i < 2 ^ (n + 1 - m)) :
    BitString.blen (jointLeftCountPayload n m i) ≤
      (n + 1 - m) + 6 * logPenalty n + 11 := by
  have hn :
      BitString.blen (BitString.ofNatExact n) ≤ logPenalty n + 1 := by
    exact le_trans (BitString.blen_ofNatExact_le_ofNat n) (blen_ofNat_le_logPenalty_succ n)
  have hmBits :
      BitString.blen (BitString.ofNatExact m) ≤ logPenalty n + 2 := by
    exact blen_ofNatExact_le_logPenalty_add_two_of_le_succ hm
  have hiBits :
      BitString.blen (BitString.ofNatExact i) ≤ n + 1 - m := by
    exact le_trans (BitString.blen_ofNatExact_le_size i) ((Nat.size_le).2 hi)
  have hheaderN :
      BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact n))) ≤
        logPenalty n + 1 := by
    exact le_trans
      (BitString.blen_ofNatExact_le_size _)
      (le_trans ((Nat.size_le).2 (BitString.blen (BitString.ofNatExact n)).lt_two_pow_self) hn)
  have hheaderM :
      BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact m))) ≤
        logPenalty n + 2 := by
    calc
      BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact m))) ≤
          BitString.blen (BitString.ofNat (BitString.blen (BitString.ofNatExact m))) :=
        BitString.blen_ofNatExact_le_ofNat _
      _ ≤ BitString.blen (BitString.ofNat (logPenalty n + 2)) := BitString.blen_ofNat_mono hmBits
      _ ≤ logPenalty n + 2 := BitString.blen_ofNat_le_self _
  rw [jointLeftCountPayload, BitString.blen_exactPairPayload, BitString.blen_exactPairPayload]
  omega

private theorem blen_ofNat_jointLeftCountPayload_le_of_index_lt {n m i : Nat}
    (hm : m ≤ n + 1)
    (hi : i < 2 ^ (n + 1 - m)) :
    BitString.blen (BitString.ofNat (BitString.blen (jointLeftCountPayload n m i))) ≤
      logPenalty n + 5 := by
  have hpayload :
      BitString.blen (jointLeftCountPayload n m i) ≤ (n + 1 - m) + 6 * logPenalty n + 11 :=
    blen_jointLeftCountPayload_le_of_index_lt hm hi
  have hlinear : BitString.blen (jointLeftCountPayload n m i) ≤ 7 * n + 12 := by
    have hlog := logPenalty_le_self n
    omega
  exact blen_ofNat_le_logPenalty_add_of_le_twoPow_mul_succ_sub_one
    (n := n) (k := 4) (by omega : BitString.blen (jointLeftCountPayload n m i) ≤ (n + 1) * 2 ^ 4 - 1)

/-- A heavy-left enumerator turns the threshold `2^m ≤ |R_x^n|` into a short prefix description of
`x`, with length `n - m + O(log n)`. -/
theorem prefixComplexity_add_threshold_le_of_jointLeftCountEnumerator
    {u x : Program} {n m : Nat}
    (hu : IsJointLeftCountEnumerator u)
    (hx : x ∈ jointLeftOutputsWithAtLeastCount n m) :
    PrefixComplexity x + m ≤ n + 8 * logPenalty n + (2 * BitString.blen u + 24) := by
  obtain ⟨i, hiCard, hrun⟩ := hu n m x hx
  have hm : m ≤ n + 1 := by
    have hpowm : 2 ^ m ≤ (jointRightOutputsUpToLength x n).length :=
      pow_le_length_jointRightOutputsUpToLength_of_mem_jointLeftOutputsWithAtLeastCount hx
    have hlenlt : (jointRightOutputsUpToLength x n).length < 2 ^ (n + 1) := by
      have hpowpos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by decide : 0 < 2)
      exact lt_of_le_of_lt (length_jointRightOutputsUpToLength_le x n) (Nat.sub_lt hpowpos (by decide))
    by_contra hm'
    have hge : n + 1 ≤ m := by omega
    have hpowge : 2 ^ (n + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hge
    exact (not_le_of_gt hlenlt) (le_trans hpowge hpowm)
  have hiPow0 :
      i < 2 ^ (n + 1 - m) - 1 := lt_of_lt_of_le hiCard (card_jointLeftOutputsWithAtLeastCount_le n m)
  have hiPow : i < 2 ^ (n + 1 - m) := by
    exact lt_of_lt_of_le hiPow0 (Nat.sub_le _ _)
  let payload : Program := jointLeftCountPayload n m i
  let p : Program := BitString.pair u (BitString.e2 payload)
  have hpRuns : PrefixRuns p [] x := by
    refine ⟨u, payload, rfl, ?_⟩
    simpa [payload] using hrun
  have hpx : PrefixComplexity x ≤ BitString.blen p := by
    simpa [PrefixComplexity] using prefixConditionalComplexity_le_length hpRuns
  have hpayload :
      BitString.blen payload ≤ (n + 1 - m) + 6 * logPenalty n + 11 := by
    simpa [payload] using blen_jointLeftCountPayload_le_of_index_lt (n := n) (m := m) hm hiPow
  have hlogPayload :
      BitString.blen (BitString.ofNat (BitString.blen payload)) ≤ logPenalty n + 5 := by
    simpa [payload] using blen_ofNat_jointLeftCountPayload_le_of_index_lt (n := n) (m := m) hm hiPow
  have hp :
      BitString.blen p ≤ (n + 1 - m) + 8 * logPenalty n + (2 * BitString.blen u + 23) := by
    have hpShape :
        BitString.blen p =
          2 * BitString.blen u + BitString.blen payload +
            2 * BitString.blen (BitString.ofNat (BitString.blen payload)) + 2 := by
      have hpShape0 :
          BitString.blen p =
            1 + (1 + (2 * BitString.blen u +
              (BitString.blen payload +
                2 * BitString.blen (BitString.ofNat (BitString.blen payload))))) := by
        simp [p, BitString.blen_pair, BitString.blen_e2, Nat.add_comm, Nat.add_left_comm]
      omega
    rw [hpShape]
    omega
  have hsum :
      PrefixComplexity x + m ≤ (n + 1 - m) + m + 8 * logPenalty n + (2 * BitString.blen u + 23) := by
    calc
      PrefixComplexity x + m ≤ BitString.blen p + m := Nat.add_le_add_right hpx m
      _ ≤ ((n + 1 - m) + 8 * logPenalty n + (2 * BitString.blen u + 23)) + m := by
        exact Nat.add_le_add_right hp m
      _ = (n + 1 - m) + m + 8 * logPenalty n + (2 * BitString.blen u + 23) := by omega
  calc
    PrefixComplexity x + m ≤ (n + 1 - m) + m + 8 * logPenalty n + (2 * BitString.blen u + 23) := hsum
    _ = n + 8 * logPenalty n + (2 * BitString.blen u + 24) := by omega

theorem mem_jointLeftOutputsWithAtLeastCount_of_pow_le_length_jointRightOutputs
    {x : Program} {n m : Nat}
    (hpow : 2 ^ m ≤ (jointRightOutputsUpToLength x n).length) :
    x ∈ jointLeftOutputsWithAtLeastCount n m := by
  have hpos : 0 < (jointRightOutputsUpToLength x n).length := by
    exact lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 2)) hpow
  let y : Program := (jointRightOutputsUpToLength x n)[0]'hpos
  have hy : y ∈ jointRightOutputsUpToLength x n := by
    dsimp [y]
    rw [List.mem_iff_getElem]
    exact ⟨0, hpos, rfl⟩
  unfold jointLeftOutputsWithAtLeastCount
  rw [List.mem_toFinset, List.mem_filterMap]
  refine ⟨packedInput x y, ?_, ?_⟩
  · exact mem_prefixOutputsUpToLength_of_mem_jointRightOutputsUpToLength hy
  · simp [hpow]

/-- A heavy-left enumerator yields the sharp fixed-`x` count bound required for the lower chain
rule, with explicit logarithmic slack. -/
theorem length_jointRightOutputsUpToLength_le_of_jointLeftCountEnumerator
    {u x : Program} {n : Nat}
    (hu : IsJointLeftCountEnumerator u) :
    (jointRightOutputsUpToLength x n).length ≤
      2 ^ (n + 8 * logPenalty n + (2 * BitString.blen u + 25) - PrefixComplexity x) := by
  let L : Nat := (jointRightOutputsUpToLength x n).length
  by_cases hL : L = 0
  · simpa [L, hL]
  · let m : Nat := Nat.log 2 L
    have hpow : 2 ^ m ≤ (jointRightOutputsUpToLength x n).length := by
      simpa [L, m] using (Nat.pow_log_le_self 2 hL)
    have hx : x ∈ jointLeftOutputsWithAtLeastCount n m :=
      mem_jointLeftOutputsWithAtLeastCount_of_pow_le_length_jointRightOutputs hpow
    have hkm :=
      prefixComplexity_add_threshold_le_of_jointLeftCountEnumerator
        (u := u) (x := x) (n := n) (m := m) hu hx
    have hmsucc :
        m + 1 ≤ n + 8 * logPenalty n + (2 * BitString.blen u + 25) - PrefixComplexity x := by
      omega
    have hlt :
        (jointRightOutputsUpToLength x n).length <
          2 ^ (n + 8 * logPenalty n + (2 * BitString.blen u + 25) - PrefixComplexity x) := by
      calc
        (jointRightOutputsUpToLength x n).length < 2 ^ (m + 1) := by
          simpa [L, m] using (Nat.lt_pow_succ_log_self Nat.one_lt_two L)
        _ ≤ 2 ^ (n + 8 * logPenalty n + (2 * BitString.blen u + 25) - PrefixComplexity x) := by
          exact Nat.pow_le_pow_right (by decide) hmsucc
    exact Nat.le_of_lt hlt

/-- Payload encoding used to specify a bounded candidate via `(n, i)`. -/
def jointRightPayload (n i : Nat) : Program :=
  BitString.exactPairPayload (BitString.ofNatExact n) (BitString.ofNatExact i)

@[simp] theorem decode_jointRightPayload (n i : Nat) :
    BitString.decodeExactPairPayload (jointRightPayload n i) =
      (BitString.ofNatExact n, BitString.ofNatExact i) := by
  simp [jointRightPayload]

/-- Specification of an interpreter that enumerates the bounded candidate family for fixed `x`. -/
def IsJointRightEnumerator (u : Program) : Prop :=
  ∀ x : Program, ∀ n : Nat, ∀ y : Program,
    y ∈ jointRightOutputsUpToLength x n →
      ∃ i < (jointRightOutputsUpToLength x n).length,
        runs u (packedInput x (jointRightPayload n i)) y

private theorem jointRightEnumeratorNat_partrec :
    Nat.Partrec fun inputNat => Nat.rfindOpt (jointRightSearchStepNat inputNat) := by
  exact Partrec.nat_iff.1 (Partrec.rfindOpt jointRightSearchStepNat_computable)

private theorem exists_jointRightEnumeratorCode :
    ∃ c : Nat.Partrec.Code,
      ∀ inputNat : Nat,
        Nat.Partrec.Code.eval c inputNat = Nat.rfindOpt (jointRightSearchStepNat inputNat) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 jointRightEnumeratorNat_partrec
  exact ⟨c, fun inputNat => by simpa using congrFun hc inputNat⟩

/-- A fixed program enumerating the bounded right-output family used in the lower-chain proof. -/
noncomputable def jointRightEnumeratorCode : Nat.Partrec.Code :=
  Classical.choose exists_jointRightEnumeratorCode

theorem eval_jointRightEnumeratorCode (inputNat : Nat) :
    Nat.Partrec.Code.eval jointRightEnumeratorCode inputNat =
      Nat.rfindOpt (jointRightSearchStepNat inputNat) :=
  Classical.choose_spec exists_jointRightEnumeratorCode inputNat

/-- Concrete program implementing the bounded right-output enumerator. -/
noncomputable def jointRightEnumerator : Program :=
  UniversalMachine.codeToProgram jointRightEnumeratorCode

@[simp] private theorem jointRightArgsOfNat_packedInput (x : Program) (n i : Nat) :
    jointRightArgsOfNat (BitString.toNatExact (packedInput x (jointRightPayload n i))) = (x, n, i) := by
  have hunpack :
      unpackInput (BitString.ofNatExact (BitString.toNatExact (packedInput x (jointRightPayload n i)))) =
        (x, jointRightPayload n i) := by
    rw [BitString.ofNatExact_toNatExact]
    exact unpackInput_packedInput x (jointRightPayload n i)
  have hpayload :
      (unpackInput (BitString.ofNatExact (BitString.toNatExact (packedInput x (jointRightPayload n i))))).2 =
        jointRightPayload n i := by
    exact congrArg Prod.snd hunpack
  rw [Prod.mk.injEq]
  constructor
  · exact congrArg Prod.fst hunpack
  · rw [Prod.mk.injEq]
    constructor
    · calc
        BitString.toNatExact
            (BitString.decodeExactPairPayload
              (unpackInput
                (BitString.ofNatExact (BitString.toNatExact (packedInput x (jointRightPayload n i))))).2).1 =
            BitString.toNatExact (BitString.ofNatExact n) := by
              rw [hpayload, decode_jointRightPayload]
        _ = n := BitString.toNatExact_ofNatExact n
    · calc
        BitString.toNatExact
            (BitString.decodeExactPairPayload
              (unpackInput
                (BitString.ofNatExact (BitString.toNatExact (packedInput x (jointRightPayload n i))))).2).2 =
            BitString.toNatExact (BitString.ofNatExact i) := by
              rw [hpayload, decode_jointRightPayload]
        _ = i := BitString.toNatExact_ofNatExact i

@[simp] private theorem jointRightSearchStepNat_packedInput (x : Program) (n i t : Nat) :
    jointRightSearchStepNat (BitString.toNatExact (packedInput x (jointRightPayload n i))) t =
      ((jointRightDiscoveredUpToStep x n t)[i]?).map BitString.toNatExact := by
  rw [jointRightSearchStepNat, jointRightArgsOfNat_packedInput]
  simp [jointRightSearchStep]

theorem jointRightEnumerator_isJointRightEnumerator : IsJointRightEnumerator jointRightEnumerator := by
  intro x n y hy
  obtain ⟨i, hi, t, ht⟩ := exists_jointRightDiscoveryIndex_of_mem hy
  refine ⟨i, hi, ?_⟩
  let inputNat := BitString.toNatExact (packedInput x (jointRightPayload n i))
  have hmono :
      ∀ {a m u}, m ≤ u →
        a ∈ jointRightSearchStepNat inputNat m →
        a ∈ jointRightSearchStepNat inputNat u := by
    intro a m u hmu hm
    rw [jointRightSearchStepNat_packedInput] at hm ⊢
    rw [Option.mem_def] at hm ⊢
    rcases hstep : (jointRightDiscoveredUpToStep x n m)[i]? with _ | y'
    · simp [hstep] at hm
    · simp [hstep] at hm
      subst a
      have hstep' : (jointRightDiscoveredUpToStep x n u)[i]? = some y' :=
        jointRightDiscoveredUpToStep_getElem?_mono hmu hstep
      simp [hstep']
  have hstepNat : BitString.toNatExact y ∈ jointRightSearchStepNat inputNat t := by
    rw [jointRightSearchStepNat_packedInput]
    simpa [Option.mem_def, ht]
  have hrfind :
      BitString.toNatExact y ∈ Nat.rfindOpt (jointRightSearchStepNat inputNat) := by
    exact (Nat.rfindOpt_mono hmono).2 ⟨t, hstepNat⟩
  rw [jointRightEnumerator, UniversalMachine.runs_codeToProgram_iff]
  have hEval :
      Nat.Partrec.Code.eval jointRightEnumeratorCode inputNat =
        Part.some (BitString.toNatExact y) := by
    calc
      Nat.Partrec.Code.eval jointRightEnumeratorCode inputNat =
          Nat.rfindOpt (jointRightSearchStepNat inputNat) :=
            eval_jointRightEnumeratorCode inputNat
      _ = Part.some (BitString.toNatExact y) := Part.eq_some_iff.2 hrfind
  change Nat.Partrec.Code.eval jointRightEnumeratorCode inputNat = Part.some (BitString.toNatExact y)
  exact hEval

private theorem blen_jointRightPayload_le_of_index_lt {n i : Nat}
    (hi : i < 2 ^ (n + 1) - 1) :
    BitString.blen (jointRightPayload n i) ≤ n + 3 * logPenalty n + 5 := by
  have hn :
      BitString.blen (BitString.ofNatExact n) ≤ logPenalty n + 1 := by
    exact le_trans (BitString.blen_ofNatExact_le_ofNat n) (blen_ofNat_le_logPenalty_succ n)
  have hiPow : i < 2 ^ (n + 1) := by
    exact lt_of_lt_of_le hi (Nat.sub_le _ _)
  have hiBits :
      BitString.blen (BitString.ofNatExact i) ≤ n + 1 := by
    exact le_trans (BitString.blen_ofNatExact_le_size i) ((Nat.size_le).2 hiPow)
  have hheader :
      BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact n))) ≤
        logPenalty n + 1 := by
    exact le_trans
      (BitString.blen_ofNatExact_le_size _)
      (le_trans ((Nat.size_le).2 (BitString.blen (BitString.ofNatExact n)).lt_two_pow_self) hn)
  rw [jointRightPayload, BitString.blen_exactPairPayload]
  omega

private theorem blen_ofNat_jointRightPayload_le_of_index_lt {n i : Nat}
    (hi : i < 2 ^ (n + 1) - 1) :
    BitString.blen (BitString.ofNat (BitString.blen (jointRightPayload n i))) ≤ logPenalty n + 4 := by
  have hpayload : BitString.blen (jointRightPayload n i) ≤ n + 3 * logPenalty n + 5 :=
    blen_jointRightPayload_le_of_index_lt hi
  have hlinear : BitString.blen (jointRightPayload n i) ≤ 4 * n + 5 := by
    have hlog := logPenalty_le_self n
    omega
  exact blen_ofNat_le_logPenalty_add_of_le_twoPow_mul_succ_sub_one
    (n := n) (k := 3) (by omega : BitString.blen (jointRightPayload n i) ≤ (n + 1) * 2 ^ 3 - 1)

private theorem blen_jointRightPayload_le_of_index_lt_pow {n i m : Nat}
    (hi : i < 2 ^ m) :
    BitString.blen (jointRightPayload n i) ≤ m + 3 * logPenalty n + 4 := by
  have hn :
      BitString.blen (BitString.ofNatExact n) ≤ logPenalty n + 1 := by
    exact le_trans (BitString.blen_ofNatExact_le_ofNat n) (blen_ofNat_le_logPenalty_succ n)
  have hiBits :
      BitString.blen (BitString.ofNatExact i) ≤ m := by
    exact le_trans (BitString.blen_ofNatExact_le_size i) ((Nat.size_le).2 hi)
  have hheader :
      BitString.blen (BitString.ofNatExact (BitString.blen (BitString.ofNatExact n))) ≤
        logPenalty n + 1 := by
    exact le_trans
      (BitString.blen_ofNatExact_le_size _)
      (le_trans ((Nat.size_le).2 (BitString.blen (BitString.ofNatExact n)).lt_two_pow_self) hn)
  rw [jointRightPayload, BitString.blen_exactPairPayload]
  omega

/-- A bounded enumerator turns a joint-complexity bound into an indexed conditional description
of `y` from `x`. This is the machine-facing enumeration lemma behind the lower-chain argument. -/
theorem prefixConditionalComplexity_logLe_of_jointRightEnumerator {u x y : Program} {n : Nat}
    (hu : IsJointRightEnumerator u)
    (hxy : JointComplexity x y ≤ n) :
    LogLe (PrefixConditionalComplexity y x) n n := by
  have hy : y ∈ jointRightOutputsUpToLength x n :=
    mem_jointRightOutputsUpToLength_of_jointComplexity_le hxy
  obtain ⟨i, hi, hrun⟩ := hu x n y hy
  let payload : Program := jointRightPayload n i
  let p : Program := BitString.pair u (BitString.e2 payload)
  have hpRuns : PrefixRuns p x y := by
    refine ⟨u, payload, rfl, ?_⟩
    simpa [payload] using hrun
  have hcond : PrefixConditionalComplexity y x ≤ BitString.blen p := by
    exact prefixConditionalComplexity_le_length hpRuns
  have hiBound : i < 2 ^ (n + 1) - 1 := by
    exact lt_of_lt_of_le hi (length_jointRightOutputsUpToLength_le x n)
  have hpayload :
      BitString.blen payload ≤ n + 3 * logPenalty n + 5 :=
    blen_jointRightPayload_le_of_index_lt hiBound
  have hlogPayload :
      BitString.blen (BitString.ofNat (BitString.blen payload)) ≤ logPenalty n + 4 := by
    simpa [payload] using blen_ofNat_jointRightPayload_le_of_index_lt (n := n) hiBound
  have hp :
      BitString.blen p ≤ n + 5 * logPenalty n + (2 * BitString.blen u + 15) := by
    have hpShape :
        BitString.blen p =
          1 + (1 + (2 * BitString.blen u +
            (BitString.blen payload +
              2 * BitString.blen (BitString.ofNat (BitString.blen payload))))) := by
      simp [p, BitString.blen_pair, BitString.blen_e2, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    have hpShape' :
        BitString.blen p =
          2 * BitString.blen u + BitString.blen payload +
            2 * BitString.blen (BitString.ofNat (BitString.blen payload)) + 2 := by
      omega
    rw [hpShape']
    omega
  exact ⟨5, 2 * BitString.blen u + 15, le_trans hcond hp⟩

/-- Exact index-to-description bound for the fixed-`x` candidate family. -/
theorem prefixConditionalComplexity_le_of_jointRightEnumerator_of_indexPow
    {u x y : Program} {n i m : Nat}
    (hrun : runs u (packedInput x (jointRightPayload n i)) y)
    (hi : i < 2 ^ m) :
    PrefixConditionalComplexity y x ≤
      m + 3 * logPenalty n +
        2 * BitString.blen (BitString.ofNat (m + 3 * logPenalty n + 4)) +
        (2 * BitString.blen u + 6) := by
  let payload : Program := jointRightPayload n i
  let p : Program := BitString.pair u (BitString.e2 payload)
  have hpRuns : PrefixRuns p x y := by
    refine ⟨u, payload, rfl, ?_⟩
    simpa [payload] using hrun
  have hcond : PrefixConditionalComplexity y x ≤ BitString.blen p := by
    exact prefixConditionalComplexity_le_length hpRuns
  have hpayload :
      BitString.blen payload ≤ m + 3 * logPenalty n + 4 :=
    blen_jointRightPayload_le_of_index_lt_pow hi
  have hlogPayload :
      BitString.blen (BitString.ofNat (BitString.blen payload)) ≤
        BitString.blen (BitString.ofNat (m + 3 * logPenalty n + 4)) := by
    exact BitString.blen_ofNat_mono hpayload
  have hp :
      BitString.blen p ≤
        m + 3 * logPenalty n +
          2 * BitString.blen (BitString.ofNat (m + 3 * logPenalty n + 4)) +
          (2 * BitString.blen u + 6) := by
    have hpShape :
        BitString.blen p =
          2 * BitString.blen u + BitString.blen payload +
            2 * BitString.blen (BitString.ofNat (BitString.blen payload)) + 2 := by
      have hpShape0 :
          BitString.blen p =
            1 + (1 + (2 * BitString.blen u +
              (BitString.blen payload +
                2 * BitString.blen (BitString.ofNat (BitString.blen payload))))) := by
        simp [p, BitString.blen_pair, BitString.blen_e2, Nat.add_comm, Nat.add_left_comm]
      omega
    rw [hpShape]
    omega
  exact le_trans hcond hp

/-- Exact count-to-description bound for the fixed-`x` candidate family. -/
theorem prefixConditionalComplexity_le_of_jointRightEnumerator_of_count
    {u x y : Program} {n c d : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x n).length ≤ 2 ^ (n + c * logPenalty n + d - PrefixComplexity x))
    (hxy : JointComplexity x y ≤ n) :
    PrefixConditionalComplexity y x ≤
      (n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n +
        2 * BitString.blen
          (BitString.ofNat
            ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
        (2 * BitString.blen u + 6) := by
  have hy : y ∈ jointRightOutputsUpToLength x n :=
    mem_jointRightOutputsUpToLength_of_jointComplexity_le hxy
  obtain ⟨i, hi', hrun⟩ := hu x n y hy
  have hiPow :
      i < 2 ^ (n + c * logPenalty n + d - PrefixComplexity x) := by
    exact lt_of_lt_of_le hi' hcount
  exact prefixConditionalComplexity_le_of_jointRightEnumerator_of_indexPow hrun hiPow

/-- Exact additive lower-chain bound from a fixed enumerator and a sharp fixed-`x` count bound. -/
theorem prefixComplexity_add_prefixConditionalComplexity_le_of_jointRightEnumerator_of_count
    {u x y : Program} {n c d k t : Nat}
    (hu : IsJointRightEnumerator u)
    (hcount :
      (jointRightOutputsUpToLength x n).length ≤ 2 ^ (n + c * logPenalty n + d - PrefixComplexity x))
    (hpx : PrefixComplexity x ≤ n + k * logPenalty n + t)
    (hxy : JointComplexity x y ≤ n) :
    PrefixComplexity x + PrefixConditionalComplexity y x ≤
      n + (c + k + 3) * logPenalty n + (d + t) +
        2 * BitString.blen
          (BitString.ofNat
            ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
        (2 * BitString.blen u + 6) := by
  let tail : Nat :=
    3 * logPenalty n +
      2 * BitString.blen
        (BitString.ofNat
          ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
      (2 * BitString.blen u + 6)
  have h :=
    prefixConditionalComplexity_le_of_jointRightEnumerator_of_count
      (u := u) (x := x) (y := y) (n := n) (c := c) (d := d) hu hcount hxy
  have h' :
      PrefixConditionalComplexity y x ≤
        (n + c * logPenalty n + d - PrefixComplexity x) + tail := by
    calc
      PrefixConditionalComplexity y x ≤
          (n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n +
            2 * BitString.blen
              (BitString.ofNat
                ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
            (2 * BitString.blen u + 6) := h
      _ = (n + c * logPenalty n + d - PrefixComplexity x) + tail := by
        simp [tail, Nat.add_assoc]
  have hcancel :
      PrefixComplexity x + (n + c * logPenalty n + d - PrefixComplexity x) ≤
        n + c * logPenalty n + d + (k * logPenalty n + t) := by
    by_cases hle : PrefixComplexity x ≤ n + c * logPenalty n + d
    · omega
    · have hgt : n + c * logPenalty n + d < PrefixComplexity x := Nat.lt_of_not_ge hle
      have hsub : n + c * logPenalty n + d - PrefixComplexity x = 0 := by
        exact Nat.sub_eq_zero_of_le hgt.le
      rw [hsub]
      omega
  have hsum :
      PrefixComplexity x + PrefixConditionalComplexity y x ≤
        PrefixComplexity x + (n + c * logPenalty n + d - PrefixComplexity x) + tail := by
    calc
      PrefixComplexity x + PrefixConditionalComplexity y x ≤
          PrefixComplexity x +
            ((n + c * logPenalty n + d - PrefixComplexity x) + tail) := by
        exact Nat.add_le_add_left h' (PrefixComplexity x)
      _ = PrefixComplexity x + (n + c * logPenalty n + d - PrefixComplexity x) + tail := by
        omega
  have hsum' :
      PrefixComplexity x + PrefixConditionalComplexity y x ≤
        n + c * logPenalty n + d + (k * logPenalty n + t) + tail := by
    exact le_trans hsum (Nat.add_le_add_right hcancel tail)
  have hmul :
      (c + k + 3) * logPenalty n = c * logPenalty n + k * logPenalty n + 3 * logPenalty n := by
    calc
      (c + k + 3) * logPenalty n = ((c + k) + 3) * logPenalty n := by omega
      _ = (c + k) * logPenalty n + 3 * logPenalty n := by rw [Nat.add_mul]
      _ = c * logPenalty n + k * logPenalty n + 3 * logPenalty n := by rw [Nat.add_mul]
  calc
    PrefixComplexity x + PrefixConditionalComplexity y x ≤
        n + c * logPenalty n + d + (k * logPenalty n + t) + tail := hsum'
    _ = n + (c + k + 3) * logPenalty n + (d + t) +
          2 * BitString.blen
            (BitString.ofNat
              ((n + c * logPenalty n + d - PrefixComplexity x) + 3 * logPenalty n + 4)) +
          (2 * BitString.blen u + 6) := by
      dsimp [tail]
      rw [hmul]
      omega

end UniversalMachine

end IcTheory
