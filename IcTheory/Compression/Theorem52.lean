import IcTheory.Compression.Theorem51
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

/-- Project-style unboundedness for a randomness test. This matches the paper's qualitative
assumption, even though the current formalization of Theorem 5.2 only uses the test structure and
an explicit decoder hypothesis. -/
def IsUnboundedMartinLofTest (δ : Program → Nat) : Prop :=
  ∀ c : Nat, ∃ x : Program, c < δ x

/-- Decode an index `i < 2^n` as a bitstring of exactly length `n`. This is the paper's padded
index encoding for residuals of length `n - m`. -/
def ofNatFixed : Nat → Nat → Program
  | 0, _ => []
  | n + 1, i =>
      let p := 2 ^ n
      if i < p then false :: ofNatFixed n i else true :: ofNatFixed n (i - p)

@[simp] theorem blen_ofNatFixed (n i : Nat) :
    BitString.blen (ofNatFixed n i) = n := by
  induction n generalizing i with
  | zero =>
      simp [ofNatFixed]
  | succ n ih =>
      by_cases h : i < 2 ^ n
      · simp [ofNatFixed, h, ih]
      · simp [ofNatFixed, h, ih]

/-- Abstract fixed decoder for the `m`-th randomness-test level set. For every `x` of length `n`
with `δ(x) ≥ m`, the decoder reconstructs `x` from some padded index of length `n - m`. This is
the exact machine-level ingredient left open by the current Theorem 5.2 formalization. -/
def IsRandomnessLevelIndexDecoder (δ : Program → Nat) (m : Nat) (f : Program) : Prop :=
  ∀ n : Nat, ∀ x : Program,
    x ∈ randomnessLevelSet δ n m →
      ∃ i < 2 ^ (n - m), runs f (ofNatFixed (n - m) i) x

/-- If a fixed decoder reconstructs every string in the `m`-th level set from a residual of length
`n - m`, and the decoder itself is shorter than `m`, then it is a feature of every string in that
level set whose length is at least `m`. -/
theorem randomnessLevelIndexDecoder_isFeature_of_lengthGap {δ : Program → Nat}
    {m : Nat} {f x : Program}
    (hdecoder : IsRandomnessLevelIndexDecoder δ m f)
    (hgap : BitString.blen f < m)
    (hmxLen : m ≤ BitString.blen x)
    (hxm : m ≤ δ x) :
    IsFeature runs f x := by
  have hxLevel : x ∈ randomnessLevelSet δ (BitString.blen x) m := by
    exact (mem_randomnessLevelSet_iff).2 ⟨rfl, hxm⟩
  obtain ⟨i, hi, hrun⟩ := hdecoder (BitString.blen x) x hxLevel
  let r := ofNatFixed (BitString.blen x - m) i
  have hrLen : BitString.blen r = BitString.blen x - m := by
    simp [r, blen_ofNatFixed]
  refine ⟨codeToProgram (Code.const (BitString.toNatExact r)), ?_⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · exact (runs_const_iff (BitString.toNatExact r) x r).2
      (BitString.ofNatExact_toNatExact r).symm
  · simpa [r] using hrun
  · unfold CompressionCondition
    rw [hrLen]
    omega

/-- Current-form Theorem 5.2. The remaining gap to the exact paper statement is the concrete
construction of `f` from the lower-semicomputable test witness. Once such a fixed decoder is
available and shorter than the chosen threshold `m`, the feature conclusion follows immediately. -/
theorem theorem52 {δ : Program → Nat}
    (hδ : IsUniformMartinLofTest δ)
    (hunbounded : IsUnboundedMartinLofTest δ)
    {m : Nat} {f : Program}
    (hdecoder : IsRandomnessLevelIndexDecoder δ m f)
    (hgap : BitString.blen f < m) :
    ∀ {x : Program}, m ≤ BitString.blen x → m ≤ δ x → IsFeature runs f x := by
  intro x hmxLen hxm
  exact randomnessLevelIndexDecoder_isFeature_of_lengthGap hdecoder hgap hmxLen hxm

end

end Compression

end IcTheory
