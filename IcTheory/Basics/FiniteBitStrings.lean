import IcTheory.Basics.BitString

namespace IcTheory

namespace BitString

/-- Exhaustive list of all bitstrings of fixed length `n`. -/
def allOfLength : Nat → List BitString
  | 0 => [[]]
  | n + 1 => (allOfLength n).map (List.cons false) ++ (allOfLength n).map (List.cons true)

@[simp] theorem mem_allOfLength_iff {x : BitString} {n : Nat} :
    x ∈ allOfLength n ↔ blen x = n := by
  induction n generalizing x with
  | zero =>
      cases x <;> simp [allOfLength, blen]
  | succ n ih =>
      cases x with
      | nil =>
          simp [allOfLength, blen]
      | cons b xs =>
          cases b <;> simp [allOfLength, ih, blen]

@[simp] theorem length_allOfLength (n : Nat) :
    (allOfLength n).length = 2 ^ n := by
  induction n with
  | zero =>
      simp [allOfLength]
  | succ n ih =>
      simp [allOfLength, ih, Nat.pow_succ]
      omega

/-- Exhaustive list of all bitstrings of length at most `n`. -/
def allUpToLength : Nat → List BitString
  | 0 => allOfLength 0
  | n + 1 => allUpToLength n ++ allOfLength (n + 1)

@[simp] theorem mem_allUpToLength_iff {x : BitString} {n : Nat} :
    x ∈ allUpToLength n ↔ blen x ≤ n := by
  induction n generalizing x with
  | zero =>
      simp [allUpToLength]
  | succ n ih =>
      simp [allUpToLength, ih]
      omega

@[simp] theorem length_allUpToLength (n : Nat) :
    (allUpToLength n).length = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero =>
      simp [allUpToLength]
  | succ n ih =>
      simp [allUpToLength, ih, Nat.pow_succ]
      omega

end BitString

end IcTheory
