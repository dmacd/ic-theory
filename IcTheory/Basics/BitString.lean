import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

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

private theorem blen_encodePosNum_eq_natSize :
    ∀ p : PosNum, (Computability.encodePosNum p).length = PosNum.natSize p
  | 1 => rfl
  | PosNum.bit0 p => by
      simp [Computability.encodePosNum, blen_encodePosNum_eq_natSize p, PosNum.natSize]
  | PosNum.bit1 p => by
      simp [Computability.encodePosNum, blen_encodePosNum_eq_natSize p, PosNum.natSize]

private theorem blen_encodeNum_eq_natSize :
    ∀ n : Num, (Computability.encodeNum n).length = Num.natSize n
  | 0 => rfl
  | Num.pos p => blen_encodePosNum_eq_natSize p

@[simp] theorem blen_ofNat_eq_size (n : Nat) : blen (ofNat n) = Nat.size n := by
  simpa [blen, ofNat, Computability.encodeNat] using
    (blen_encodeNum_eq_natSize (n : Num)).trans (Num.natSize_to_nat (n : Num))

theorem blen_ofNat_mono {m n : Nat} (h : m ≤ n) :
    blen (ofNat m) ≤ blen (ofNat n) := by
  rw [blen_ofNat_eq_size, blen_ofNat_eq_size]
  exact Nat.size_le_size h

theorem blen_ofNat_le_self (n : Nat) : blen (ofNat n) ≤ n := by
  rw [blen_ofNat_eq_size]
  exact Nat.size_le.2 n.lt_two_pow_self

theorem blen_ofNatExact_le_size (n : Nat) : blen (ofNatExact n) ≤ Nat.size n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
      simp [ofNatExact]
  | succ n =>
      rw [ofNatExact, blen_cons]
      cases hb : Nat.bodd n
      · have ih' := ih n.div2 (by
          simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2))
        have hn : n = 2 * n.div2 := by
          simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
        have hsucc : n.succ = Nat.bit true n.div2 := by
          rw [hn, Nat.bit_val]
          simp
        have hbit : Nat.bit true n.div2 ≠ 0 := by
          rw [Nat.bit_val]
          simp
        have hs : Nat.size (n + 1) = Nat.size (Nat.bit true n.div2) := by
          simpa using congrArg Nat.size hsucc
        rw [hs, Nat.size_bit hbit]
        exact Nat.succ_le_succ ih'
      · have ih' := ih n.div2 (by
          simpa [Nat.div2_val] using Nat.lt_succ_of_le (Nat.div_le_self n 2))
        have hn : n = 2 * n.div2 + 1 := by
          simpa [Nat.bit_val, hb] using (Nat.bit_bodd_div2 n).symm
        have hsucc : n.succ = Nat.bit false (n.div2 + 1) := by
          calc
            n.succ = 2 * n.div2 + 2 := by omega
            _ = 2 * (n.div2 + 1) := by omega
            _ = Nat.bit false (n.div2 + 1) := by simp [Nat.bit_val]
        have hbit : Nat.bit false (n.div2 + 1) ≠ 0 := by
          rw [Nat.bit_val]
          simp
        have hs : Nat.size (n + 1) = Nat.size (Nat.bit false (n.div2 + 1)) := by
          simpa using congrArg Nat.size hsucc
        rw [hs, Nat.size_bit hbit]
        exact Nat.succ_le_succ (le_trans ih' (Nat.size_le_size (Nat.le_succ _)))

theorem blen_ofNatExact_le_ofNat (n : Nat) : blen (ofNatExact n) ≤ blen (ofNat n) := by
  rw [blen_ofNat_eq_size]
  exact blen_ofNatExact_le_size n

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
