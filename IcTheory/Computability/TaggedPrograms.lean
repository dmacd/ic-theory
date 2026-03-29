import IcTheory.Computability.ProgramEncoding
import IcTheory.Basics.InternalEncoding
import Mathlib.Tactic

namespace IcTheory

namespace UniversalMachine

inductive OuterTag where
  | direct
  | prefixReplay
  | postcompose
  | invalid
deriving DecidableEq

/-- Two-bit tag used for ordinary compiled `Nat.Partrec.Code` payloads. -/
def directTag : Program := [false, false]

/-- Two-bit tag used for programs that replay a stored prefix description. -/
def prefixReplayTag : Program := [true, false]

/-- Two-bit tag used for programs that postcompose two stored plain programs. -/
def postcomposeTag : Program := [false, true]

/-- Outer-machine encoding of a direct `Nat.Partrec.Code` payload. -/
def directProgram (payload : Program) : Program :=
  directTag ++ payload

/-- Outer-machine encoding of a stored prefix program. -/
def prefixReplayProgram (q : Program) : Program :=
  prefixReplayTag ++ q

/-- Outer-machine encoding of a stored postcomposition pair `(g, p)`. -/
def postcomposeProgram (g p : Program) : Program :=
  postcomposeTag ++ BitString.exactPairPayload g p

/-- Read the outer two-bit tag and return the remaining payload. -/
def decodeOuterTag : Program → OuterTag × Program
  | false :: false :: payload => (OuterTag.direct, payload)
  | true :: false :: payload => (OuterTag.prefixReplay, payload)
  | false :: true :: payload => (OuterTag.postcompose, payload)
  | payload => (OuterTag.invalid, payload)

/-- Decode the public paper-style pairing `pair x y = e1 x ++ y`. -/
def decodePairPayload (payload : Program) : Program × Program :=
  let n := BitString.countLeadingTrue payload
  let rest := (BitString.splitAt (n + 1) payload).2
  BitString.splitAt n rest

/-- Decode the public `e2` self-delimiting payload format. -/
def decodeE2Payload (payload : Program) : Program :=
  let n := BitString.countLeadingTrue payload
  let rest := (BitString.splitAt (n + 1) payload).2
  (BitString.splitAt n rest).2

/-- Decode a stored prefix description `pair interpreter (e2 payload)`. -/
def decodePrefixDescription (q : Program) : Program × Program :=
  let desc := decodePairPayload q
  (desc.1, decodeE2Payload desc.2)

@[simp] theorem decodePairPayload_pair (x y : Program) :
    decodePairPayload (BitString.pair x y) = (x, y) := by
  let k := BitString.blen x
  have hk : BitString.countLeadingTrue (BitString.pair x y) = k := by
    simpa [k, BitString.pair, BitString.e1, BitString.unaryHeader, Nat.add_assoc] using
      (BitString.countLeadingTrue_unaryHeader k (x ++ y))
  have hsplit₁ :
      BitString.splitAt (k + 1) (BitString.pair x y) = (BitString.unaryHeader k, x ++ y) := by
    simpa [k, BitString.pair, BitString.e1] using
      (BitString.splitAt_eq_take_drop (k + 1) (BitString.unaryHeader k ++ x ++ y))
  have hrest :
      (BitString.splitAt (k + 1) (BitString.pair x y)).2 = x ++ y := by
    simpa using congrArg Prod.snd hsplit₁
  have hsplit₂ :
      BitString.splitAt k (x ++ y) = (x, y) := by
    simpa [k, BitString.splitAt_eq_take_drop] using
      (BitString.splitAt_eq_take_drop k (x ++ y))
  unfold decodePairPayload
  simp [hk, hrest, hsplit₂]

@[simp] theorem decodeE2Payload_e2 (x : Program) :
    decodeE2Payload (BitString.e2 x) = x := by
  let k := BitString.blen (BitString.ofNat (BitString.blen x))
  have hk : BitString.countLeadingTrue (BitString.e2 x) = k := by
    simpa [k, BitString.e2, BitString.e1, BitString.unaryHeader, Nat.add_assoc] using
      (BitString.countLeadingTrue_unaryHeader k (BitString.ofNat (BitString.blen x) ++ x))
  have hsplit₁ :
      BitString.splitAt (k + 1) (BitString.e2 x) =
        (BitString.unaryHeader k, BitString.ofNat (BitString.blen x) ++ x) := by
    simpa [k, BitString.e2, BitString.e1] using
      (BitString.splitAt_eq_take_drop
        (k + 1)
        (BitString.unaryHeader k ++ BitString.ofNat (BitString.blen x) ++ x))
  have hrest :
      (BitString.splitAt (k + 1) (BitString.e2 x)).2 =
        BitString.ofNat (BitString.blen x) ++ x := by
    simpa using congrArg Prod.snd hsplit₁
  have hsplit₂ :
      BitString.splitAt k (BitString.ofNat (BitString.blen x) ++ x) =
        (BitString.ofNat (BitString.blen x), x) := by
    simpa [k, BitString.splitAt_eq_take_drop] using
      (BitString.splitAt_eq_take_drop k (BitString.ofNat (BitString.blen x) ++ x))
  have hrest₂ :
      (BitString.splitAt k (BitString.ofNat (BitString.blen x) ++ x)).2 = x := by
    simpa using congrArg Prod.snd hsplit₂
  unfold decodeE2Payload
  simp [hk, hrest, hrest₂]

@[simp] theorem decodePrefixDescription_pair_e2 (interpreter payload : Program) :
    decodePrefixDescription (BitString.pair interpreter (BitString.e2 payload)) =
      (interpreter, payload) := by
  simp [decodePrefixDescription]

@[simp] theorem decodeOuterTag_directProgram (payload : Program) :
    decodeOuterTag (directProgram payload) = (OuterTag.direct, payload) := by
  simp [decodeOuterTag, directProgram, directTag]

@[simp] theorem decodeOuterTag_prefixReplayProgram (q : Program) :
    decodeOuterTag (prefixReplayProgram q) = (OuterTag.prefixReplay, q) := by
  simp [decodeOuterTag, prefixReplayProgram, prefixReplayTag]

@[simp] theorem decodeOuterTag_postcomposeProgram (g p : Program) :
    decodeOuterTag (postcomposeProgram g p) =
      (OuterTag.postcompose, BitString.exactPairPayload g p) := by
  simp [decodeOuterTag, postcomposeProgram, postcomposeTag]

@[simp] theorem blen_directProgram (payload : Program) :
    BitString.blen (directProgram payload) = BitString.blen payload + 2 := by
  simp [directProgram, directTag, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem blen_prefixReplayProgram (q : Program) :
    BitString.blen (prefixReplayProgram q) = BitString.blen q + 2 := by
  simp [prefixReplayProgram, prefixReplayTag, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem blen_postcomposeProgram (g p : Program) :
    BitString.blen (postcomposeProgram g p) =
      BitString.blen (BitString.exactPairPayload g p) + 2 := by
  simp [postcomposeProgram, postcomposeTag, Nat.add_comm, Nat.add_left_comm]
  omega

theorem splitAt_fst_blen_le (n : Nat) (xs : Program) :
    BitString.blen (BitString.splitAt n xs).1 ≤ BitString.blen xs := by
  rw [BitString.splitAt_eq_take_drop]
  simpa [BitString.blen] using (List.length_take_le n xs)

theorem splitAt_snd_blen_le (n : Nat) (xs : Program) :
    BitString.blen (BitString.splitAt n xs).2 ≤ BitString.blen xs := by
  rw [BitString.splitAt_eq_take_drop]
  simp [BitString.blen, List.length_drop]

theorem decodePairPayload_fst_blen_le (payload : Program) :
    BitString.blen (decodePairPayload payload).1 ≤ BitString.blen payload := by
  unfold decodePairPayload
  exact le_trans
    (splitAt_fst_blen_le _ ((BitString.splitAt (BitString.countLeadingTrue payload + 1) payload).2))
    (splitAt_snd_blen_le _ payload)

theorem decodePairPayload_snd_blen_le (payload : Program) :
    BitString.blen (decodePairPayload payload).2 ≤ BitString.blen payload := by
  unfold decodePairPayload
  exact le_trans
    (splitAt_snd_blen_le _ ((BitString.splitAt (BitString.countLeadingTrue payload + 1) payload).2))
    (splitAt_snd_blen_le _ payload)

theorem decodeE2Payload_blen_le (payload : Program) :
    BitString.blen (decodeE2Payload payload) ≤ BitString.blen payload := by
  unfold decodeE2Payload
  exact le_trans
    (splitAt_snd_blen_le _ ((BitString.splitAt (BitString.countLeadingTrue payload + 1) payload).2))
    (splitAt_snd_blen_le _ payload)

theorem decodePrefixDescription_interp_blen_le (q : Program) :
    BitString.blen (decodePrefixDescription q).1 ≤ BitString.blen q := by
  unfold decodePrefixDescription
  exact decodePairPayload_fst_blen_le q

theorem decodePrefixDescription_payload_blen_le (q : Program) :
    BitString.blen (decodePrefixDescription q).2 ≤ BitString.blen q := by
  unfold decodePrefixDescription
  exact le_trans (decodeE2Payload_blen_le (decodePairPayload q).2)
    (decodePairPayload_snd_blen_le q)

theorem decodeExactPairPayload_fst_blen_le (payload : Program) :
    BitString.blen (BitString.decodeExactPairPayload payload).1 ≤ BitString.blen payload := by
  unfold BitString.decodeExactPairPayload
  set lenCodeBits := BitString.countLeadingTrue payload
  set rest₁ := (BitString.splitAt (lenCodeBits + 1) payload).2
  set lenCode := (BitString.splitAt lenCodeBits rest₁).1
  set rest₂ := (BitString.splitAt lenCodeBits rest₁).2
  exact le_trans
    (splitAt_fst_blen_le (BitString.toNatExact lenCode) rest₂)
    (le_trans
      (splitAt_snd_blen_le lenCodeBits rest₁)
      (splitAt_snd_blen_le (lenCodeBits + 1) payload))

theorem decodeExactPairPayload_snd_blen_le (payload : Program) :
    BitString.blen (BitString.decodeExactPairPayload payload).2 ≤ BitString.blen payload := by
  unfold BitString.decodeExactPairPayload
  set lenCodeBits := BitString.countLeadingTrue payload
  set rest₁ := (BitString.splitAt (lenCodeBits + 1) payload).2
  set lenCode := (BitString.splitAt lenCodeBits rest₁).1
  set rest₂ := (BitString.splitAt lenCodeBits rest₁).2
  exact le_trans
    (splitAt_snd_blen_le (BitString.toNatExact lenCode) rest₂)
    (le_trans
      (splitAt_snd_blen_le lenCodeBits rest₁)
      (splitAt_snd_blen_le (lenCodeBits + 1) payload))

theorem left_blen_lt_postcomposeProgram (g p : Program) :
    BitString.blen g < BitString.blen (postcomposeProgram g p) := by
  rw [blen_postcomposeProgram, BitString.blen_exactPairPayload]
  omega

theorem right_blen_lt_postcomposeProgram (g p : Program) :
    BitString.blen p < BitString.blen (postcomposeProgram g p) := by
  rw [blen_postcomposeProgram, BitString.blen_exactPairPayload]
  omega

theorem decodePairPayload_computable : Computable decodePairPayload := by
  unfold decodePairPayload
  exact Computable.pair
    (Computable.fst.comp (BitString.splitAt_computable.comp
      BitString.countLeadingTrue_computable
      ((Computable.snd.comp
        (BitString.splitAt_computable.comp
          (Computable.succ.comp BitString.countLeadingTrue_computable)
          Computable.id)))))
    (Computable.snd.comp
      (BitString.splitAt_computable.comp
        BitString.countLeadingTrue_computable
        ((Computable.snd.comp
          (BitString.splitAt_computable.comp
            (Computable.succ.comp BitString.countLeadingTrue_computable)
            Computable.id)))))

theorem decodeE2Payload_computable : Computable decodeE2Payload := by
  unfold decodeE2Payload
  exact Computable.snd.comp
    (BitString.splitAt_computable.comp
      BitString.countLeadingTrue_computable
      ((Computable.snd.comp
        (BitString.splitAt_computable.comp
          (Computable.succ.comp BitString.countLeadingTrue_computable)
          Computable.id))))

theorem decodePrefixDescription_computable : Computable decodePrefixDescription := by
  unfold decodePrefixDescription
  exact Computable.pair
    (Computable.fst.comp decodePairPayload_computable)
    (decodeE2Payload_computable.comp (Computable.snd.comp decodePairPayload_computable))

end UniversalMachine

end IcTheory
