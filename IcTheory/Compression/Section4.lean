import IcTheory.Compression.Theorem39
import Mathlib.Tactic

namespace IcTheory

namespace Compression

open UniversalMachine
open Nat.Partrec

noncomputable section

/-- Section 4 autoencoder payload `a = g' f`, stored as the paper-style self-delimiting
codeword `⟨g, e2(f)⟩`. -/
def autoencoderPayload (g f : Program) : Program :=
  BitString.pair g (BitString.e2 f)

/-- Decode an autoencoder payload into its descriptive map and feature. -/
def decodeAutoencoderPayload (a : Program) : Program × Program :=
  decodePrefixDescription a

@[simp] theorem decodeAutoencoderPayload_autoencoderPayload (g f : Program) :
    decodeAutoencoderPayload (autoencoderPayload g f) = (g, f) := by
  simp [decodeAutoencoderPayload, autoencoderPayload]

@[simp] theorem autoencoderPayload_eq_iff
    {g₁ f₁ g₂ f₂ : Program} :
    autoencoderPayload g₁ f₁ = autoencoderPayload g₂ f₂ ↔
      g₁ = g₂ ∧ f₁ = f₂ := by
  constructor
  · intro h
    rcases BitString.pair_eq_pair_iff.mp h with ⟨hg, hf⟩
    exact ⟨hg, BitString.e2_injective hf⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Recognize the valid self-delimiting Section 4 autoencoder codewords. -/
def IsAutoencoderPayload (a : Program) : Prop :=
  autoencoderPayload (decodeAutoencoderPayload a).1 (decodeAutoencoderPayload a).2 = a

instance instDecidableIsAutoencoderPayload (a : Program) :
    Decidable (IsAutoencoderPayload a) := by
  unfold IsAutoencoderPayload
  infer_instance

@[simp] theorem isAutoencoderPayload_autoencoderPayload (g f : Program) :
    IsAutoencoderPayload (autoencoderPayload g f) := by
  simp [IsAutoencoderPayload]

theorem isAutoencoderPayload_iff_exists {a : Program} :
    IsAutoencoderPayload a ↔ ∃ g f, autoencoderPayload g f = a := by
  constructor
  · intro h
    exact ⟨(decodeAutoencoderPayload a).1, (decodeAutoencoderPayload a).2, h⟩
  · rintro ⟨g, f, rfl⟩
    exact isAutoencoderPayload_autoencoderPayload g f

/-- Section 4 machine output `⟨y, r, f⟩`, encoded through the exact bitstring bridge. -/
def autoencoderOutput (y r f : Program) : Program :=
  BitString.ofNatExact (Nat.pair (BitString.toNatExact y)
    (Nat.pair (BitString.toNatExact r) (BitString.toNatExact f)))

/-- Decode an autoencoder output into reconstructed string, residual, and feature. -/
def decodeAutoencoderOutput (out : Program) : Program × Program × Program :=
  let yr := (BitString.toNatExact out).unpair
  let rf := yr.2.unpair
  (BitString.ofNatExact yr.1, BitString.ofNatExact rf.1, BitString.ofNatExact rf.2)

@[simp] theorem decodeAutoencoderOutput_autoencoderOutput (y r f : Program) :
    decodeAutoencoderOutput (autoencoderOutput y r f) = (y, r, f) := by
  simp [decodeAutoencoderOutput, autoencoderOutput]

/-- A successful Section 4 autoencoder step for the current string `x`. -/
def AutoencoderStep (x g f r : Program) : Prop :=
  runs g x r ∧ runs f r x ∧ CompressionCondition f r x

theorem autoencoderStep_isDescriptiveMap {x g f r : Program}
    (h : AutoencoderStep x g f r) :
    IsDescriptiveMap runs f g x := by
  exact ⟨r, h.1, h.2.1, h.2.2⟩

theorem autoencoderStep_isFeature {x g f r : Program}
    (h : AutoencoderStep x g f r) :
    IsFeature runs f x := by
  exact ⟨g, autoencoderStep_isDescriptiveMap h⟩

private def autoencoderDecoded (n : Nat) : Program × Program :=
  decodeAutoencoderPayload (BitString.ofNatExact n.unpair.2)

private theorem decodeAutoencoderPayload_computable : Computable decodeAutoencoderPayload :=
  decodePrefixDescription_computable

private theorem autoencoderDecoded_computable : Computable autoencoderDecoded := by
  exact decodeAutoencoderPayload_computable.comp
    (BitString.ofNatExact_computable.comp (Computable.snd.comp Computable.unpair))

private def autoencoderMapCodeNat (n : Nat) : Nat :=
  BitString.toNatExact (autoencoderDecoded n).1

private def autoencoderFeatureCodeNat (n : Nat) : Nat :=
  BitString.toNatExact (autoencoderDecoded n).2

private theorem autoencoderMapCodeNat_computable : Computable autoencoderMapCodeNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.fst.comp autoencoderDecoded_computable)

private theorem autoencoderFeatureCodeNat_computable : Computable autoencoderFeatureCodeNat := by
  exact BitString.toNatExact_computable.comp
    (Computable.snd.comp autoencoderDecoded_computable)

private theorem evalAutoencoderInterpreter_partrec :
    Nat.Partrec fun n =>
      Code.eval (storedProgramCode (autoencoderMapCodeNat n)) n.unpair.1 >>= fun rNat =>
        Code.eval (storedProgramCode (autoencoderFeatureCodeNat n)) rNat >>= fun yNat =>
          Part.some (Nat.pair yNat (Nat.pair rNat (autoencoderFeatureCodeNat n))) := by
  have hOuter : Computable fun n : Nat => n.unpair.1 := by
    exact Computable.fst.comp Computable.unpair
  have hMapCode : Computable fun n => storedProgramCode (autoencoderMapCodeNat n) := by
    exact storedProgramCode_computable.comp autoencoderMapCodeNat_computable
  have hEvalMap : _root_.Partrec fun n =>
      Code.eval (storedProgramCode (autoencoderMapCodeNat n)) n.unpair.1 := by
    exact Code.eval_part.comp hMapCode hOuter
  have hFeatureCode : Computable fun p : Nat × Nat =>
      storedProgramCode (autoencoderFeatureCodeNat p.1) := by
    exact storedProgramCode_computable.comp
      (autoencoderFeatureCodeNat_computable.comp Computable.fst)
  have hFeatureInput : Computable fun p : Nat × Nat => p.2 := by
    exact Computable.snd
  have hEvalFeature : _root_.Partrec fun p : Nat × Nat =>
      Code.eval (storedProgramCode (autoencoderFeatureCodeNat p.1)) p.2 := by
    exact Code.eval_part.comp hFeatureCode hFeatureInput
  have hPack : _root_.Partrec₂ fun n rNat =>
      Code.eval (storedProgramCode (autoencoderFeatureCodeNat n)) rNat >>= fun yNat =>
        Part.some (Nat.pair yNat (Nat.pair rNat (autoencoderFeatureCodeNat n))) := by
    have hOut : Computable₂ fun (p : Nat × Nat) (yNat : Nat) =>
        Nat.pair yNat (Nat.pair p.2 (autoencoderFeatureCodeNat p.1)) := by
      exact (Primrec₂.natPair.to_comp).comp Computable.snd
        ((Primrec₂.natPair.to_comp).comp
          (Computable.snd.comp Computable.fst)
          (autoencoderFeatureCodeNat_computable.comp
            (Computable.fst.comp Computable.fst)))
    simpa using (hEvalFeature.bind hOut.partrec₂).to₂
  exact _root_.Partrec.nat_iff.1 (hEvalMap.bind hPack)

theorem exists_autoencoderInterpreterCode :
    ∃ c : Code, ∀ n : Nat,
      Code.eval c n =
        Code.eval (storedProgramCode (autoencoderMapCodeNat n)) n.unpair.1 >>= fun rNat =>
          Code.eval (storedProgramCode (autoencoderFeatureCodeNat n)) rNat >>= fun yNat =>
            Part.some (Nat.pair yNat (Nat.pair rNat (autoencoderFeatureCodeNat n))) := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 evalAutoencoderInterpreter_partrec
  exact ⟨c, fun n => by simpa using congrFun hc n⟩

/-- Concrete Section 4 machine `W`. It decodes an autoencoder `a = g' f`, runs `g` on `x`,
then `f` on the residual, and returns `⟨y, r, f⟩`. -/
noncomputable def autoencoderInterpreterCode : Code :=
  Classical.choose exists_autoencoderInterpreterCode

theorem eval_autoencoderInterpreterCode (n : Nat) :
    Code.eval autoencoderInterpreterCode n =
      Code.eval (storedProgramCode (autoencoderMapCodeNat n)) n.unpair.1 >>= fun rNat =>
        Code.eval (storedProgramCode (autoencoderFeatureCodeNat n)) rNat >>= fun yNat =>
          Part.some (Nat.pair yNat (Nat.pair rNat (autoencoderFeatureCodeNat n))) :=
  Classical.choose_spec exists_autoencoderInterpreterCode n

/-- Fixed machine `W` from Section 4. -/
noncomputable def autoencoderInterpreter : Program :=
  codeToProgram autoencoderInterpreterCode

@[simp] theorem runs_autoencoderInterpreter_output_iff
    (x g f y r f' : Program) :
    runs autoencoderInterpreter (packedInput x (autoencoderPayload g f))
      (autoencoderOutput y r f') ↔
        f' = f ∧ runs g x r ∧ runs f r y := by
  rw [autoencoderInterpreter, runs_codeToProgram_iff, toNatExact_packedInput]
  constructor
  · intro h
    have h' :
        (Code.eval (storedProgramCode (BitString.toNatExact g)) (BitString.toNatExact x) >>=
          fun rNat =>
            Code.eval (storedProgramCode (BitString.toNatExact f)) rNat >>= fun yNat =>
              Part.some (Nat.pair yNat (Nat.pair rNat (BitString.toNatExact f)))) =
          Part.some
            (Nat.pair (BitString.toNatExact y)
              (Nat.pair (BitString.toNatExact r) (BitString.toNatExact f'))) := by
      simpa [eval_autoencoderInterpreterCode, autoencoderMapCodeNat, autoencoderFeatureCodeNat,
        autoencoderDecoded, autoencoderPayload, autoencoderOutput, decodeAutoencoderPayload] using h
    have h'' :
        ∃ rNat,
          rNat ∈ Code.eval (storedProgramCode (BitString.toNatExact g)) (BitString.toNatExact x) ∧
            Nat.pair (BitString.toNatExact y)
                (Nat.pair (BitString.toNatExact r) (BitString.toNatExact f')) ∈
              (Code.eval (storedProgramCode (BitString.toNatExact f)) rNat >>= fun yNat =>
                Part.some (Nat.pair yNat (Nat.pair rNat (BitString.toNatExact f)))) := by
      simpa [Bind.bind, Part.eq_some_iff, Part.mem_bind_iff] using h'
    rcases h'' with ⟨rNat, hrMem, hrest⟩
    have hrest' :
        ∃ yNat,
          yNat ∈ Code.eval (storedProgramCode (BitString.toNatExact f)) rNat ∧
            Nat.pair (BitString.toNatExact y)
                (Nat.pair (BitString.toNatExact r) (BitString.toNatExact f')) ∈
              Part.some (Nat.pair yNat (Nat.pair rNat (BitString.toNatExact f))) := by
      simpa [Bind.bind, Part.mem_bind_iff] using hrest
    rcases hrest' with ⟨yNat, hyMem, hpackMem⟩
    have hrNat :
        Code.eval (storedProgramCode (BitString.toNatExact g)) (BitString.toNatExact x) =
          Part.some rNat := Part.eq_some_iff.2 hrMem
    have hyNat :
        Code.eval (storedProgramCode (BitString.toNatExact f)) rNat = Part.some yNat :=
      Part.eq_some_iff.2 hyMem
    have hpack :
        Nat.pair (BitString.toNatExact y)
            (Nat.pair (BitString.toNatExact r) (BitString.toNatExact f')) =
          Nat.pair yNat (Nat.pair rNat (BitString.toNatExact f)) := by
      simpa using hpackMem
    have hpairOuter :
        BitString.toNatExact y = yNat ∧
          Nat.pair (BitString.toNatExact r) (BitString.toNatExact f') =
            Nat.pair rNat (BitString.toNatExact f) := by
      exact Nat.pair_eq_pair.mp hpack
    have hpairInner :
        BitString.toNatExact r = rNat ∧ BitString.toNatExact f' = BitString.toNatExact f := by
      exact Nat.pair_eq_pair.mp hpairOuter.2
    have hfEq : f' = f := by
      exact BitString.toNatExact_injective hpairInner.2
    exact ⟨hfEq, by simpa [runs, programToCode, hpairInner.1] using hrNat,
      by simpa [runs, programToCode, hpairInner.1, hpairOuter.1] using hyNat⟩
  · rintro ⟨rfl, hgRuns, hfRuns⟩
    have hg' :
        Code.eval (programToCode g) (BitString.toNatExact x) =
          Part.some (BitString.toNatExact r) := by
      simpa [runs] using hgRuns
    have hf' :
        Code.eval (programToCode f') (BitString.toNatExact r) =
          Part.some (BitString.toNatExact y) := by
      simpa [runs] using hfRuns
    rw [eval_autoencoderInterpreterCode]
    simp [autoencoderMapCodeNat, autoencoderFeatureCodeNat, autoencoderDecoded, autoencoderPayload,
      autoencoderOutput, decodeAutoencoderPayload]
    rw [hg', Part.bind_some, hf', Part.bind_some]

@[simp] theorem runs_autoencoderInterpreter_iff
    (x g f y r : Program) :
    runs autoencoderInterpreter (packedInput x (autoencoderPayload g f))
      (autoencoderOutput y r f) ↔
        runs g x r ∧ runs f r y := by
  simpa using (runs_autoencoderInterpreter_output_iff x g f y r f)

/-- Pure acceptance predicate used by the search routines in Section 4. -/
def SearchAutoencoderAccepts (x a : Program) : Prop :=
  ∃ r f : Program,
    runs autoencoderInterpreter (packedInput x a) (autoencoderOutput x r f) ∧
      CompressionCondition f r x

theorem searchAutoencoderAccepts_iff {x g f : Program} :
    SearchAutoencoderAccepts x (autoencoderPayload g f) ↔
      ∃ r : Program, AutoencoderStep x g f r := by
  constructor
  · rintro ⟨r, f', hruns, hcomp⟩
    rcases (runs_autoencoderInterpreter_output_iff x g f x r f').mp hruns with
      ⟨rfl, hgRuns, hfRuns⟩
    refine ⟨r, ?_⟩
    exact ⟨hgRuns, hfRuns, hcomp⟩
  · rintro ⟨r, hgRuns, hfRuns, hcomp⟩
    refine ⟨r, f, ?_, hcomp⟩
    exact (runs_autoencoderInterpreter_iff x g f x r).2 ⟨hgRuns, hfRuns⟩

/-- Programs considered in phase `i` of the Section 4 dovetailing search: precisely the valid
self-delimiting autoencoder codewords of length at most `i`. -/
def phasePrograms (i : Nat) : List Program :=
  (BitString.allUpToLength i).filter (fun a => decide (IsAutoencoderPayload a))

@[simp] theorem mem_phasePrograms_iff {a : Program} {i : Nat} :
    a ∈ phasePrograms i ↔ IsAutoencoderPayload a ∧ BitString.blen a ≤ i := by
  constructor
  · intro ha
    rcases List.mem_filter.1 ha with ⟨hmem, hvalid⟩
    exact ⟨by simpa using hvalid, BitString.mem_allUpToLength_iff.1 hmem⟩
  · rintro ⟨hvalid, hlen⟩
    exact List.mem_filter.2 ⟨BitString.mem_allUpToLength_iff.2 hlen, by simpa using hvalid⟩

/-- Number of machine steps allocated to program `a` in phase `i`. -/
def phaseBudget (i : Nat) (a : Program) : Nat :=
  if IsAutoencoderPayload a ∧ BitString.blen a ≤ i then 2 ^ (i - BitString.blen a) else 0

theorem phaseBudget_eq_pow_of_mem_phasePrograms {a : Program} {i : Nat}
    (ha : a ∈ phasePrograms i) :
    phaseBudget i a = 2 ^ (i - BitString.blen a) := by
  simp [phaseBudget, (mem_phasePrograms_iff.mp ha).1, (mem_phasePrograms_iff.mp ha).2]

/-- Search-tree node used by ALICE: current residual together with the feature path collected so
far in forward order `f₁, ..., fₛ`. -/
structure AliceNode where
  residual : Program
  features : List Program

/-- Root of the ALICE search tree. -/
def AliceNode.root (x : Program) : AliceNode :=
  ⟨x, []⟩

/-- Extend an ALICE node by one accepted autoencoder step. -/
def AliceNode.extend (node : AliceNode) (r f : Program) : AliceNode :=
  ⟨r, node.features ++ [f]⟩

/-- Concrete description object attached to a search-tree node. -/
def AliceNode.description (node : AliceNode) : Program :=
  schemeDescription node.residual node.features

@[simp] theorem AliceNode_root_residual (x : Program) :
    (AliceNode.root x).residual = x := rfl

@[simp] theorem AliceNode_root_features (x : Program) :
    (AliceNode.root x).features = [] := rfl

@[simp] theorem AliceNode_extend_residual (node : AliceNode) (r f : Program) :
    (node.extend r f).residual = r := rfl

@[simp] theorem AliceNode_extend_features (node : AliceNode) (r f : Program) :
    (node.extend r f).features = node.features ++ [f] := rfl

/-- Search-tree branches explored by ALICE. -/
inductive IsAliceBranch (x : Program) : AliceNode → Prop
  | root : IsAliceBranch x (AliceNode.root x)
  | step {node : AliceNode} {g f r : Program}
      (hnode : IsAliceBranch x node)
      (hstep : AutoencoderStep node.residual g f r) :
      IsAliceBranch x (node.extend r f)

/-- Greedy-ALICE uses the same node shape as ALICE, but only follows a single branch. -/
abbrev GreedyAliceState := AliceNode

/-- One greedy step picks some accepted autoencoder and replaces the current residual by its
output residual. -/
def GreedyAliceStep (state next : GreedyAliceState) : Prop :=
  ∃ g f r : Program,
    AutoencoderStep state.residual g f r ∧
      next = state.extend r f

theorem greedyAliceStep_iff {state next : GreedyAliceState} :
    GreedyAliceStep state next ↔
      ∃ g f r : Program,
        runs g state.residual r ∧
          runs f r state.residual ∧
          CompressionCondition f r state.residual ∧
          next = state.extend r f := by
  constructor
  · rintro ⟨g, f, r, hstep, rfl⟩
    exact ⟨g, f, r, hstep.1, hstep.2.1, hstep.2.2, rfl⟩
  · rintro ⟨g, f, r, hg, hf, hcomp, rfl⟩
    exact ⟨g, f, r, ⟨hg, hf, hcomp⟩, rfl⟩

end

end Compression

end IcTheory
