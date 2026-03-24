import IcTheory.Basics.Pairing

namespace IcTheory

namespace BitString

/-- An internal self-delimiting length code based on the exact bitstring bridge. -/
def exactLengthCode (x : BitString) : BitString :=
  e1 (ofNatExact (blen x))

/-- An internal pair encoding with additive length
`|x| + |y| + O(log |x|)`.
This is not the paper's public pairing; it is a machine-facing payload format. -/
def exactPairPayload (x y : BitString) : BitString :=
  exactLengthCode x ++ x ++ y

@[simp] theorem blen_exactLengthCode (x : BitString) :
    blen (exactLengthCode x) = 2 * blen (ofNatExact (blen x)) + 1 := by
  simp [exactLengthCode]

@[simp] theorem blen_exactPairPayload (x y : BitString) :
    blen (exactPairPayload x y) =
      blen x + blen y + (2 * blen (ofNatExact (blen x)) + 1) := by
  simp [exactPairPayload, exactLengthCode, Nat.add_assoc, Nat.add_comm]

/-- Count the initial run of `true` bits. -/
def countLeadingTrue : BitString → Nat
  | true :: xs => countLeadingTrue xs + 1
  | _ => 0

/-- Split a bitstring after `n` many bits. -/
def splitAt : Nat → BitString → BitString × BitString
  | 0, xs => ([], xs)
  | _ + 1, [] => ([], [])
  | n + 1, x :: xs =>
      let ys := splitAt n xs
      (x :: ys.1, ys.2)

@[simp] theorem countLeadingTrue_nil : countLeadingTrue ([] : BitString) = 0 := rfl

@[simp] theorem countLeadingTrue_false (xs : BitString) :
    countLeadingTrue (false :: xs) = 0 := rfl

@[simp] theorem countLeadingTrue_true (xs : BitString) :
    countLeadingTrue (true :: xs) = countLeadingTrue xs + 1 := rfl

@[simp] theorem splitAt_zero (xs : BitString) : splitAt 0 xs = ([], xs) := rfl

@[simp] theorem splitAt_nil (n : Nat) : splitAt (n + 1) ([] : BitString) = ([], []) := rfl

@[simp] theorem splitAt_cons (n : Nat) (x : Bool) (xs : BitString) :
    splitAt (n + 1) (x :: xs) = (x :: (splitAt n xs).1, (splitAt n xs).2) := rfl

theorem splitAt_eq_take_drop : ∀ n : Nat, ∀ xs : BitString,
    splitAt n xs = (xs.take n, xs.drop n)
  | 0, xs => by simp [splitAt]
  | n + 1, [] => by simp [splitAt]
  | n + 1, x :: xs => by
      simp [splitAt, splitAt_eq_take_drop n xs]

@[simp] theorem countLeadingTrue_unary (n : Nat) :
    countLeadingTrue (unary n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [unary, Computability.unaryEncodeNat, ih]

@[simp] theorem countLeadingTrue_unaryHeader (n : Nat) (xs : BitString) :
    countLeadingTrue (unaryHeader n ++ xs) = n := by
  induction n with
  | zero =>
      simp [unaryHeader, unary, Computability.unaryEncodeNat]
  | succ n ih =>
      simpa [unaryHeader, unary, Computability.unaryEncodeNat, countLeadingTrue] using
        congrArg Nat.succ ih

/-- Decode the internal pair payload by reading the exact length code and then splitting
off that many bits. -/
def decodeExactPairPayload (payload : BitString) : BitString × BitString :=
  let lenCodeBits := countLeadingTrue payload
  let rest₁ := (splitAt (lenCodeBits + 1) payload).2
  let lenCode := (splitAt lenCodeBits rest₁).1
  let rest₂ := (splitAt lenCodeBits rest₁).2
  splitAt (toNatExact lenCode) rest₂

@[simp] theorem decodeExactPairPayload_exactPairPayload (x y : BitString) :
    decodeExactPairPayload (exactPairPayload x y) = (x, y) := by
  let k := blen (ofNatExact (blen x))
  have hk : countLeadingTrue (e1 (ofNatExact (blen x)) ++ x ++ y) = k := by
    simpa [k, e1, unaryHeader, Nat.add_assoc] using
      (countLeadingTrue_unaryHeader k ((ofNatExact (blen x)) ++ x ++ y))
  have hsplit₁ :
      splitAt (k + 1) (e1 (ofNatExact (blen x)) ++ x ++ y) =
        (unaryHeader k, ofNatExact (blen x) ++ x ++ y) := by
    simpa [k, e1, splitAt_eq_take_drop]
      using (splitAt_eq_take_drop (k + 1) (e1 (ofNatExact (blen x)) ++ x ++ y))
  have hsplit₂ :
      splitAt k (ofNatExact (blen x) ++ x ++ y) = (ofNatExact (blen x), x ++ y) := by
    simpa [k, splitAt_eq_take_drop]
      using (splitAt_eq_take_drop k (ofNatExact (blen x) ++ x ++ y))
  have hrest₁ :
      (splitAt (k + 1) (e1 (ofNatExact (blen x)) ++ x ++ y)).2 =
        ofNatExact (blen x) ++ x ++ y := by
    simpa using congrArg Prod.snd hsplit₁
  have hlenCode :
      (splitAt k (ofNatExact (blen x) ++ x ++ y)).1 = ofNatExact (blen x) := by
    simpa using congrArg Prod.fst hsplit₂
  have hrest₂ :
      (splitAt k (ofNatExact (blen x) ++ x ++ y)).2 = x ++ y := by
    simpa using congrArg Prod.snd hsplit₂
  simp_rw [decodeExactPairPayload, exactPairPayload, exactLengthCode]
  simp_rw [hk]
  simp_rw [hrest₁]
  simp_rw [hlenCode]
  simp_rw [hrest₂]
  rw [toNatExact_ofNatExact, splitAt_eq_take_drop]
  simp

end BitString

end IcTheory
