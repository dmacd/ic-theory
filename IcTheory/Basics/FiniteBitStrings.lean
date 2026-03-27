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

@[simp] theorem nodup_allOfLength (n : Nat) :
    (allOfLength n).Nodup := by
  induction n with
  | zero =>
      simp [allOfLength]
  | succ n ih =>
      refine List.nodup_append.2 ?_
      refine ⟨?_, ?_, ?_⟩
      · simpa [allOfLength] using ih.map (show Function.Injective (List.cons false) from fun _ _ h => by
          simpa using congrArg List.tail h)
      · simpa [allOfLength] using ih.map (show Function.Injective (List.cons true) from fun _ _ h => by
          simpa using congrArg List.tail h)
      · intro x hxFalse y hxTrue hxy
        rcases List.mem_map.1 hxFalse with ⟨u, hu, rfl⟩
        rcases List.mem_map.1 hxTrue with ⟨v, hv, hvEq⟩
        have : false = true := by
          simpa using congrArg List.head? (hvEq.trans hxy.symm)
        cases this

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

@[simp] theorem nodup_allUpToLength (n : Nat) :
    (allUpToLength n).Nodup := by
  induction n with
  | zero =>
      simpa [allUpToLength] using nodup_allOfLength 0
  | succ n ih =>
      refine List.nodup_append.2 ?_
      refine ⟨ih, nodup_allOfLength (n + 1), ?_⟩
      intro x hxUp y hxEq hxy
      have hle : blen x ≤ n := mem_allUpToLength_iff.1 hxUp
      have heq : blen y = n + 1 := mem_allOfLength_iff.1 hxEq
      have hxeq : blen x = n + 1 := by simpa [hxy] using heq
      rw [hxeq] at hle
      omega

end BitString

end IcTheory
