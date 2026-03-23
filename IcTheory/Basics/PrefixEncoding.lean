import IcTheory.Basics.BitString

namespace IcTheory

namespace BitString

/-- The unary prefix `1^n 0` used by the paper. -/
def unaryHeader (n : Nat) : BitString := unary n ++ [false]

/-- The paper's first self-delimiting code `E1(x) = 1^{|x|} 0 x`. -/
def e1 (x : BitString) : BitString := unaryHeader (blen x) ++ x

/-- A second length-prefixing layer, built from `encodeNat` and `e1`. -/
def e2 (x : BitString) : BitString := e1 (ofNat (blen x)) ++ x

@[simp] theorem blen_unaryHeader (n : Nat) : blen (unaryHeader n) = n + 1 := by
  simp [unaryHeader]

@[simp] theorem blen_e1 (x : BitString) : blen (e1 x) = 2 * blen x + 1 := by
  simp [e1, unaryHeader, two_mul, Nat.add_assoc]

@[simp] theorem blen_e2 (x : BitString) : blen (e2 x) = 2 * blen (ofNat (blen x)) + blen x + 1 := by
  simp [e2, e1, unaryHeader, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem self_delimiting_overhead_e1 (x : BitString) : blen (e1 x) = blen x + (blen x + 1) := by
  simp [blen_e1, two_mul, Nat.add_assoc]

theorem self_delimiting_overhead_e2 (x : BitString) :
    blen (e2 x) = blen x + (2 * blen (ofNat (blen x)) + 1) := by
  simp [blen_e2, Nat.add_left_comm, Nat.add_comm]

end BitString

end IcTheory
