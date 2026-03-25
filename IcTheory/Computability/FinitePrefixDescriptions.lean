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

/-- Add an optional newly discovered output to the end of an output list, unless it is already
present. -/
def appendIfNew (xs : List Program) (oy : Option Program) : List Program :=
  match oy with
  | none => xs
  | some y => if y ∈ xs then xs else xs ++ [y]

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

/-- Payload encoding used to specify a heavy-left candidate via `(n, m, i)`. -/
def jointLeftCountPayload (n m i : Nat) : Program :=
  BitString.exactPairPayload (BitString.ofNatExact n)
    (BitString.exactPairPayload (BitString.ofNatExact m) (BitString.ofNatExact i))

/-- Specification of an interpreter enumerating the heavy-left family at threshold `2^m`. -/
def IsJointLeftCountEnumerator (u : Program) : Prop :=
  ∀ n m i : Nat, ∀ x : Program,
    (jointLeftOutputsWithAtLeastCountList n m)[i]? = some x →
      runs u (packedInput [] (jointLeftCountPayload n m i)) x

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
  obtain ⟨i, hiCard, hget⟩ := exists_jointLeftIndex_of_mem hx
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
    simpa [payload, jointLeftOutputsWithAtLeastCountList] using hu n m i x hget
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
  ∀ x : Program, ∀ n i : Nat, ∀ y : Program,
    (jointRightOutputsUpToLength x n)[i]? = some y →
      runs u (packedInput x (jointRightPayload n i)) y

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
  obtain ⟨i, hi, hget⟩ := exists_jointRightIndex_of_jointComplexity_le (x := x) (y := y) hxy
  let payload : Program := jointRightPayload n i
  let p : Program := BitString.pair u (BitString.e2 payload)
  have hpRuns : PrefixRuns p x y := by
    refine ⟨u, payload, rfl, ?_⟩
    simpa [payload] using hu x n i y hget
  have hcond : PrefixConditionalComplexity y x ≤ BitString.blen p := by
    exact prefixConditionalComplexity_le_length hpRuns
  have hpayload :
      BitString.blen payload ≤ n + 3 * logPenalty n + 5 :=
    blen_jointRightPayload_le_of_index_lt hi
  have hlogPayload :
      BitString.blen (BitString.ofNat (BitString.blen payload)) ≤ logPenalty n + 4 := by
    simpa [payload] using blen_ofNat_jointRightPayload_le_of_index_lt (n := n) hi
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
    (hu : IsJointRightEnumerator u)
    (hget : (jointRightOutputsUpToLength x n)[i]? = some y)
    (hi : i < 2 ^ m) :
    PrefixConditionalComplexity y x ≤
      m + 3 * logPenalty n +
        2 * BitString.blen (BitString.ofNat (m + 3 * logPenalty n + 4)) +
        (2 * BitString.blen u + 6) := by
  let payload : Program := jointRightPayload n i
  let p : Program := BitString.pair u (BitString.e2 payload)
  have hpRuns : PrefixRuns p x y := by
    refine ⟨u, payload, rfl, ?_⟩
    simpa [payload] using hu x n i y hget
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
  obtain ⟨i, _, hget⟩ := exists_jointRightIndex_of_jointComplexity_le (x := x) (y := y) hxy
  have hi' : i < (jointRightOutputsUpToLength x n).length := by
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hiPow :
      i < 2 ^ (n + c * logPenalty n + d - PrefixComplexity x) := by
    exact lt_of_lt_of_le hi' hcount
  exact prefixConditionalComplexity_le_of_jointRightEnumerator_of_indexPow hu hget hiPow

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
