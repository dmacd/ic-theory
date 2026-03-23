import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Bits

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

/-- An exact bijection from bitstrings to naturals, used for the computability bridge. -/
def toNatExact : BitString → Nat
  | [] => 0
  | false :: x => 2 * toNatExact x + 1
  | true :: x => 2 * toNatExact x + 2

/-- The inverse of `toNatExact`, giving an exact decoding from naturals to bitstrings. -/
def ofNatExact : Nat → BitString
  | 0 => []
  | n + 1 => n.bodd :: ofNatExact n.div2
termination_by n => n
decreasing_by
  simp_wf
  simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2)

@[simp] theorem blen_nil : blen ([] : BitString) = 0 := rfl

@[simp] theorem blen_cons (b : Bool) (x : BitString) : blen (b :: x) = blen x + 1 := by
  simp [blen]

@[simp] theorem blen_append (x y : BitString) : blen (x ++ y) = blen x + blen y := by
  simp [blen]

@[simp] theorem blen_singleton (b : Bool) : blen ([b] : BitString) = 1 := rfl

@[simp] theorem blen_unary (n : Nat) : blen (unary n) = n := by
  simpa [unary, blen, Computability.unaryDecodeNat] using Computability.unary_decode_encode_nat n

@[simp] theorem blen_ofNat (n : Nat) : blen (ofNat n) = (Computability.encodeNat n).length := rfl

@[simp] theorem toNatExact_ofNatExact (n : Nat) : toNatExact (ofNatExact n) = n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
      simp [ofNatExact, toNatExact]
  | succ n =>
      rw [ofNatExact]
      cases hb : Nat.bodd n
      · have ih' := ih n.div2 (by
          simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2))
        simp [toNatExact, ih']
        have h0 : n = 2 * n.div2 := by
          simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
        omega
      · have ih' := ih n.div2 (by
          simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2))
        simp [toNatExact, ih']
        have h1 : n = 2 * n.div2 + 1 := by
          simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
        omega

@[simp] theorem ofNatExact_toNatExact : ∀ x : BitString, ofNatExact (toNatExact x) = x
  | [] => by
      simp [ofNatExact, toNatExact]
  | false :: x => by
      rw [toNatExact, ofNatExact]
      simp [Nat.div2_bit0, ofNatExact_toNatExact]
  | true :: x => by
      rw [toNatExact, ofNatExact]
      simp [ofNatExact_toNatExact]

theorem toNatExact_injective : Function.Injective toNatExact := by
  intro x y h
  simpa [ofNatExact_toNatExact x, ofNatExact_toNatExact y] using congrArg ofNatExact h

end BitString

end IcTheory
