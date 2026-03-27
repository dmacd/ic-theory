import IcTheory.Computability
import IcTheory.Compression.Section32
import IcTheory.Compression.Theorem39
import IcTheory.Compression.Section4

namespace IcTheory

namespace Sanity

open Compression
open BitString
open UniversalMachine

example : blen [true, false, true] = 3 := rfl

example : e1 [true, false] = [true, true, false, true, false] := rfl

example : e2 [true, false] = [true, true, false, false, true, true, false] := rfl

example : pair [true] [false, true] = [true, false, true] ++ [false, true] := rfl

example :
    decodeExactPairPayload (exactPairPayload [true, false] [false, true]) =
      ([true, false], [false, true]) := by
  simp

example : CompressionCondition [true] [false] [true, false, true] := by
  decide

def toyRuns (_p _input output : BitString) : Prop :=
  output = [false] ∨ output = [true, false, true]

def sampleX : BitString := [true, false, true]
def sampleResidual : BitString := [false]
def sampleProgram : Program := []

example : IsDescriptiveMap toyRuns sampleProgram sampleProgram sampleX := by
  refine ⟨sampleResidual, ?_, ?_, ?_⟩
  · left
    rfl
  · right
    rfl
  · decide

example : sampleProgram ∈ descriptiveMaps toyRuns sampleProgram sampleX := by
  exact show IsDescriptiveMap toyRuns sampleProgram sampleProgram sampleX from by
    refine ⟨sampleResidual, ?_, ?_, ?_⟩
    · left
      rfl
    · right
      rfl
    · decide

example : sampleResidual ∈ residualDescriptions toyRuns sampleProgram sampleX := by
  refine ⟨sampleProgram, ?_, ?_, ?_⟩
  · left
    rfl
  · right
    rfl
  · decide

example : IsFeature toyRuns sampleProgram sampleX := by
  refine ⟨sampleProgram, ?_⟩
  refine ⟨sampleResidual, ?_, ?_, ?_⟩
  · left
    rfl
  · right
    rfl
  · decide

example : runs (codeToProgram Nat.Partrec.Code.zero) [true, false, true] [] := by
  simpa using (runs_zero_iff [true, false, true] []).2 rfl

example : runs (codeToProgram Nat.Partrec.Code.id) [true, false, true] [true, false, true] := by
  exact (runs_id_iff [true, false, true] [true, false, true]).2 rfl

example : runs (codeToProgram (Nat.Partrec.Code.const 5)) [] (ofNatExact 5) := by
  exact (runs_const_iff 5 [] (ofNatExact 5)).2 rfl

example : UniversalMachine.ConditionalComplexity [true, false, true] [] ≤
    blen (codeToProgram (Nat.Partrec.Code.const (toNatExact [true, false, true]))) := by
  apply UniversalMachine.conditionalComplexity_le_length
  exact (runs_const_iff (toNatExact [true, false, true]) [] [true, false, true]).2
    (ofNatExact_toNatExact [true, false, true]).symm

example : runs universalFeature (codeToProgram (Nat.Partrec.Code.const 5)) (ofNatExact 5) := by
  rw [runs_universalFeature_iff]
  exact (runs_const_iff 5 [] (ofNatExact 5)).2 rfl

example : PrefixRuns (pair applyInterpreter (e2 []))
    (codeToProgram (Nat.Partrec.Code.const 5)) (ofNatExact 5) := by
  apply prefixRuns_applyInterpreter_of_runs
  exact (runs_const_iff 5 [] (ofNatExact 5)).2 rfl

example : PrefixRuns (pair emptyInterpreter (e2 (codeToProgram (Nat.Partrec.Code.const 5))))
    [] (ofNatExact 5) := by
  apply prefixRuns_emptyInterpreter_of_runs
  exact (runs_const_iff 5 [] (ofNatExact 5)).2 rfl

example : PrefixRuns (pair outerApplyInterpreter (e2 (codeToProgram (Nat.Partrec.Code.const 5))))
    [] (ofNatExact 5) := by
  apply prefixRuns_outerApplyInterpreter_of_runs
  exact (runs_const_iff 5 [] (ofNatExact 5)).2 rfl

example :
    runs jointUpperInterpreter
      (packedInput []
        (JointUpperPayload []
          (codeToProgram (Nat.Partrec.Code.const 5))
          []
          (codeToProgram (Nat.Partrec.Code.const 7))))
      (packedInput (ofNatExact 5) (ofNatExact 7)) := by
  apply jointUpperInterpreter_isJointUpperInterpreter
  · exact (runs_const_iff 5 (packedInput [] []) (ofNatExact 5)).2 rfl
  · exact (runs_const_iff 7 (packedInput (ofNatExact 5) []) (ofNatExact 7)).2 rfl

example :
    runs postComposeInterpreter
      (packedInput []
        (JointUpperPayload []
          (codeToProgram (Nat.Partrec.Code.const 5))
          []
          (codeToProgram (Nat.Partrec.Code.const 7))))
      (ofNatExact 7) := by
  apply postComposeInterpreter_isPostComposeInterpreter
  · exact (runs_const_iff 5 (packedInput [] []) (ofNatExact 5)).2 rfl
  · exact (runs_const_iff 7 (packedInput (ofNatExact 5) []) (ofNatExact 7)).2 rfl

example :
    runs swapJoint
      (packedInput (packedInput (ofNatExact 5) (ofNatExact 7)) [])
      (packedInput (ofNatExact 7) (ofNatExact 5)) := by
  simpa using runs_swapJoint_iff (ofNatExact 5) (ofNatExact 7)

example :
    PrefixConditionalComplexity (ofNatExact 5) (codeToProgram (Nat.Partrec.Code.const 5)) ≤
      residualPrefixOverhead [] := by
  simpa using
    (Compression.lemma32_exact_upper
      (f := codeToProgram (Nat.Partrec.Code.const 5))
      (r := [])
      (x := ofNatExact 5)
      ((runs_const_iff 5 [] (ofNatExact 5)).2 rfl))

example : LogLe (PrefixComplexity (ofNatExact 5)) (blen (ofNatExact 5)) (blen (ofNatExact 5)) := by
  exact prefixComplexity_log_upper (ofNatExact 5)

example :
    LogLe (PrefixComplexity (ofNatExact 5))
      (Complexity (ofNatExact 5))
      (Complexity (ofNatExact 5)) := by
  exact prefixComplexity_logLe_complexity (ofNatExact 5)

example :
    LogLe (PrefixConditionalComplexity (ofNatExact 5) [])
      (ConditionalComplexity (ofNatExact 5) [])
      (ConditionalComplexity (ofNatExact 5) []) := by
  exact prefixConditionalComplexity_logLe_conditionalComplexity (ofNatExact 5) []

example :
    PrefixRuns (pair schemeDescriptionPrefixInterpreter (e2 (schemeDescription [] []))) [] [] := by
  apply prefixRuns_schemeDescription_of_runs
  simpa using
    (schemeDescriptionInterpreter_runs_of_storedPrograms
      (storedFs := []) (r := []) (x := [])
      (RunsStoredProgramList.nil []))

example :
    decodeAutoencoderPayload
      (autoencoderPayload (codeToProgram Nat.Partrec.Code.zero) (codeToProgram Nat.Partrec.Code.id)) =
        (codeToProgram Nat.Partrec.Code.zero, codeToProgram Nat.Partrec.Code.id) := by
  simp

example :
    runs autoencoderInterpreter
      (packedInput (ofNatExact 5)
        (autoencoderPayload
          (codeToProgram (Nat.Partrec.Code.const 5))
          (codeToProgram Nat.Partrec.Code.id)))
      (autoencoderOutput
        (ofNatExact 5)
        (ofNatExact 5)
        (codeToProgram Nat.Partrec.Code.id)) := by
  apply (runs_autoencoderInterpreter_iff
    (x := ofNatExact 5)
    (g := codeToProgram (Nat.Partrec.Code.const 5))
    (f := codeToProgram Nat.Partrec.Code.id)
    (y := ofNatExact 5)
    (r := ofNatExact 5)).2
  constructor
  · exact (runs_const_iff 5 (ofNatExact 5) (ofNatExact 5)).2 rfl
  · exact (runs_id_iff (ofNatExact 5) (ofNatExact 5)).2 rfl

example :
    ofNatExact 5 ∈ phasePrograms 4 := by
  rw [mem_phasePrograms_iff]
  have hlen : blen (ofNatExact 5) ≤ 3 := by
    calc
      blen (ofNatExact 5) ≤ blen (ofNat 5) := blen_ofNatExact_le_ofNat 5
      _ = Nat.size 5 := blen_ofNat_eq_size 5
      _ = 3 := by decide
  omega

end Sanity

end IcTheory
