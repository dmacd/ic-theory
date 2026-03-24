import IcTheory.Computability

namespace IcTheory

namespace Sanity

open Compression
open BitString
open UniversalMachine

example : blen [true, false, true] = 3 := rfl

example : e1 [true, false] = [true, true, false, true, false] := rfl

example : e2 [true, false] = [true, true, false, false, true, true, false] := rfl

example : pair [true] [false, true] = [true, false, true] ++ [false, true] := rfl

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

end Sanity

end IcTheory
