import IcTheory.Basics.PrefixEncoding
import Mathlib.Tactic

namespace IcTheory

namespace BitString

/-- Prefix-based pairing of binary strings, matching the paper's `⟨x, y⟩ = E1(x) ++ y` idea. -/
def pair (x y : BitString) : BitString := e1 x ++ y

/-- Triple encoding by iterated pairing. -/
def pair3 (x y z : BitString) : BitString := pair x (pair y z)

@[simp] theorem blen_pair (x y : BitString) : blen (pair x y) = 2 * blen x + blen y + 1 := by
  rw [pair, blen_append, blen_e1]
  omega

@[simp] theorem blen_pair3 (x y z : BitString) :
    blen (pair3 x y z) = 2 * blen x + 2 * blen y + blen z + 2 := by
  rw [pair3, blen_pair, blen_pair]
  omega

theorem pair_nonempty_left (x y : BitString) : pair x y ≠ [] := by
  simp [pair, e1, unaryHeader]

end BitString

end IcTheory
