import IcTheory.Computability.PrefixInformation
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

/-- Finite list of all outputs produced from `input` by prefix descriptions of length at most
`n`. -/
noncomputable def prefixOutputsUpToLength (input : Program) (n : Nat) : List Program :=
  ((BitString.allUpToLength n).filterMap fun p => prefixOutput p input).dedup

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
  ((prefixOutputsUpToLength [] n).filterMap fun z =>
    let w := unpackInput z
    if w.1 = x then some w.2 else none).dedup

theorem mem_jointRightOutputsUpToLength_of_jointComplexity_le {x y : Program} {n : Nat}
    (hxy : JointComplexity x y ≤ n) :
    y ∈ jointRightOutputsUpToLength x n := by
  unfold jointRightOutputsUpToLength
  rw [List.mem_dedup, List.mem_filterMap]
  refine ⟨packedInput x y, mem_prefixOutputsUpToLength_of_jointComplexity_le hxy, ?_⟩
  simp

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
