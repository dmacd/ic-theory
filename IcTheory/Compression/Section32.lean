import IcTheory.Compression.Section31
import IcTheory.Computability.PrefixComplexity
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine

noncomputable section

/-- The explicit self-delimiting overhead in the Lemma 3.2 prefix witness. -/
def residualPrefixOverhead (r : BitString) : Nat :=
  2 * BitString.blen (BitString.ofNat (BitString.blen r)) +
    applyInterpreterPrefixOverhead

/-- Lemma 3.2, first inequality in exact form:
the fixed prefix witness gives a concrete upper bound on `K(x | f)`. -/
theorem lemma32_exact_upper {f r x : Program} (hf : runs f r x) :
    PrefixConditionalComplexity x f ≤ BitString.blen r + residualPrefixOverhead r := by
  have h := prefixConditionalComplexity_le_applyInterpreter hf
  rw [BitString.blen_pair, BitString.blen_e2] at h
  unfold residualPrefixOverhead applyInterpreterPrefixOverhead
  omega

/-- Lemma 3.2 in exact form, before translating the encoding term into `O(log l(r))`. -/
theorem lemma32_exact {f r x : Program}
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    PrefixConditionalComplexity x f <
      (BitString.blen x - BitString.blen f) + residualPrefixOverhead r := by
  have hupper := lemma32_exact_upper hf
  unfold CompressionCondition at hcomp
  unfold residualPrefixOverhead at *
  omega

theorem residualPrefixOverhead_logLe (r : BitString) :
    LogLe (BitString.blen r + residualPrefixOverhead r) (BitString.blen r) (BitString.blen r) := by
  refine ⟨2, applyInterpreterPrefixOverhead + 2, ?_⟩
  have hlog := blen_ofNat_le_logPenalty_succ (BitString.blen r)
  unfold residualPrefixOverhead logPenalty at *
  omega

/-- Lemma 3.2, first inequality in paper form. -/
theorem lemma32_log_upper {f r x : Program} (hf : runs f r x) :
    LogLe (PrefixConditionalComplexity x f) (BitString.blen r) (BitString.blen r) := by
  obtain ⟨c, d, hrd⟩ := residualPrefixOverhead_logLe r
  exact ⟨c, d, le_trans (lemma32_exact_upper hf) hrd⟩

/-- Lemma 3.2 in paper form:
the extra cost of conditioning on `f` instead of `r` is only logarithmic. -/
theorem lemma32_log {f r x : Program}
    (hf : runs f r x)
    (hcomp : CompressionCondition f r x) :
    LogLe (PrefixConditionalComplexity x f)
      (BitString.blen x - BitString.blen f)
      (BitString.blen x) := by
  refine ⟨2, applyInterpreterPrefixOverhead + 2, ?_⟩
  have hexact := lemma32_exact hf hcomp
  have hrx : BitString.blen r ≤ BitString.blen x := by
    unfold CompressionCondition at hcomp
    omega
  have hmono := BitString.blen_ofNat_mono hrx
  have hlog := blen_ofNat_le_logPenalty_succ (BitString.blen x)
  unfold residualPrefixOverhead logPenalty at *
  omega

end

end Compression

end IcTheory
