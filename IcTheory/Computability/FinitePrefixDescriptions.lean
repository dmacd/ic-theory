import IcTheory.Computability.PrefixInformation
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

/-- Finite list of all outputs produced from `input` by prefix descriptions of length at most
`n`. -/
noncomputable def prefixOutputsUpToLength (input : Program) (n : Nat) : List Program :=
  (BitString.allUpToLength n).filterMap fun p => prefixOutput p input

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
  rw [List.mem_filterMap]
  exact ⟨p, by simpa using (BitString.mem_allUpToLength_iff.mpr hlen), by simpa using hp⟩

theorem length_prefixOutputsUpToLength_le (input : Program) (n : Nat) :
    (prefixOutputsUpToLength input n).length ≤ 2 ^ (n + 1) - 1 := by
  unfold prefixOutputsUpToLength
  exact le_trans
    (length_filterMap_le (fun p => prefixOutput p input) (BitString.allUpToLength n))
    (by simp)

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

/-- Decode a packed pair back into its two exact bitstring components. -/
def unpackInput (z : Program) : Program × Program :=
  let n := BitString.toNatExact z
  (BitString.ofNatExact n.unpair.1, BitString.ofNatExact n.unpair.2)

@[simp] theorem unpackInput_packedInput (x y : Program) :
    unpackInput (packedInput x y) = (x, y) := by
  simp [unpackInput, toNatExact_packedInput]

/-- For fixed left component `x`, this is the finite family of right components appearing in
joint descriptions of complexity at most `n`. -/
noncomputable def jointRightOutputsUpToLength (x : Program) (n : Nat) : List Program :=
  (prefixOutputsUpToLength [] n).filterMap fun z =>
    let w := unpackInput z
    if w.1 = x then some w.2 else none

theorem mem_jointRightOutputsUpToLength_of_jointComplexity_le {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    y ∈ jointRightOutputsUpToLength x n := by
  unfold jointRightOutputsUpToLength
  rw [List.mem_filterMap]
  refine ⟨packedInput x y, mem_prefixOutputsUpToLength_of_jointComplexity_le hxy, ?_⟩
  simp

theorem length_jointRightOutputsUpToLength_le (x : Program) (n : Nat) :
    (jointRightOutputsUpToLength x n).length ≤ 2 ^ (n + 1) - 1 := by
  unfold jointRightOutputsUpToLength
  exact le_trans
    (length_filterMap_le
      (fun z =>
        let w := unpackInput z
        if w.1 = x then some w.2 else none)
      (prefixOutputsUpToLength [] n))
    (length_prefixOutputsUpToLength_le [] n)

end UniversalMachine

end IcTheory
