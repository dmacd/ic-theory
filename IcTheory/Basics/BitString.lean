import Mathlib.Computability.Encoding

namespace IcTheory

/-- The paper works with finite binary strings. We model them as `List Bool`. -/
abbrev BitString := List Bool

namespace BitString

/-- The length of a bitstring. This name keeps later statements close to the paper. -/
abbrev blen : BitString → Nat := List.length

/-- Mathlib's binary encoding of naturals, reused as our default bitstring encoding of `Nat`. -/
abbrev ofNat : Nat → BitString := Computability.encodeNat

/-- A unary string of `n` many `1` bits. -/
abbrev unary : Nat → BitString := Computability.unaryEncodeNat

@[simp] theorem blen_nil : blen ([] : BitString) = 0 := rfl

@[simp] theorem blen_cons (b : Bool) (x : BitString) : blen (b :: x) = blen x + 1 := by
  simp [blen]

@[simp] theorem blen_append (x y : BitString) : blen (x ++ y) = blen x + blen y := by
  simp [blen]

@[simp] theorem blen_singleton (b : Bool) : blen ([b] : BitString) = 1 := rfl

@[simp] theorem blen_unary (n : Nat) : blen (unary n) = n := by
  simpa [unary, blen, Computability.unaryDecodeNat] using Computability.unary_decode_encode_nat n

@[simp] theorem blen_ofNat (n : Nat) : blen (ofNat n) = (Computability.encodeNat n).length := rfl

end BitString

end IcTheory
