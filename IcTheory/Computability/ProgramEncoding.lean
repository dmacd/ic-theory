import IcTheory.Compression.Feature
import Mathlib.Computability.PartrecCode

namespace IcTheory

namespace UniversalMachine

open Nat.Partrec

private def zeroTag : Nat := 15
private def succTag : Nat := 16
private def leftTag : Nat := 17
private def rightTag : Nat := 18
private def pairTag : Nat := 19
private def compTag : Nat := 20
private def precTag : Nat := 21
private def rfindTag : Nat := 22

private def zeroBits : Program := [false, false, false, false]
private def succBits : Program := [true, false, false, false]
private def leftBits : Program := [false, true, false, false]
private def rightBits : Program := [true, true, false, false]
private def pairBits : Program := [false, false, true, false]
private def compBits : Program := [true, false, true, false]
private def precBits : Program := [false, true, true, false]
private def rfindBits : Program := [true, true, true, false]

/-- Candidate additive serialization for `Nat.Partrec.Code`, isolated from the active machine. -/
def additiveCodeToProgram : Code → Program
  | .zero => zeroBits
  | .succ => succBits
  | .left => leftBits
  | .right => rightBits
  | .pair cf cg => pairBits ++ additiveCodeToProgram cf ++ additiveCodeToProgram cg
  | .comp cf cg => compBits ++ additiveCodeToProgram cf ++ additiveCodeToProgram cg
  | .prec cf cg => precBits ++ additiveCodeToProgram cf ++ additiveCodeToProgram cg
  | .rfind' cf => rfindBits ++ additiveCodeToProgram cf

private def encodeTokensRev : Code → List Nat
  | .zero => [zeroTag]
  | .succ => [succTag]
  | .left => [leftTag]
  | .right => [rightTag]
  | .pair cf cg => encodeTokensRev cg ++ encodeTokensRev cf ++ [pairTag]
  | .comp cf cg => encodeTokensRev cg ++ encodeTokensRev cf ++ [compTag]
  | .prec cf cg => encodeTokensRev cg ++ encodeTokensRev cf ++ [precTag]
  | .rfind' cf => encodeTokensRev cf ++ [rfindTag]

private def decodeTagNat : Nat → Option Nat
  | n =>
      bif n == zeroTag then some zeroTag
      else bif n == succTag then some succTag
      else bif n == leftTag then some leftTag
      else bif n == rightTag then some rightTag
      else bif n == pairTag then some pairTag
      else bif n == compTag then some compTag
      else bif n == precTag then some precTag
      else bif n == rfindTag then some rfindTag
      else none

private abbrev TokenizeState := Program × Option (List Nat)

private def stepTokenize (st : TokenizeState) (b : Bool) : TokenizeState :=
  Option.casesOn st.2 st fun toks =>
    let pending := st.1 ++ [b]
    bif BitString.blen pending == 4 then
      ([], (decodeTagNat (BitString.toNatExact pending)).map fun tok => tok :: toks)
    else
      (pending, some toks)

private def tokenizeReverse (p : Program) : Option (List Nat) :=
  match p.foldl stepTokenize ([], some []) with
  | ([], toks) => toks
  | _ => none

private def parseUnaryStack (mk : Code → Code) (stk : List Code) : Option (List Code) :=
  Option.bind stk.head? fun c => some (mk c :: stk.tail)

private def parseBinaryStack (mk : Code → Code → Code) (stk : List Code) : Option (List Code) :=
  Option.bind stk.head? fun cf =>
    Option.bind stk.tail.head? fun cg =>
      some (mk cf cg :: stk.tail.tail)

private def stepParseRev (stk : Option (List Code)) (tok : Nat) : Option (List Code) :=
  match stk with
  | Option.none => Option.none
  | some stk =>
      bif tok == zeroTag then some (Code.zero :: stk)
      else bif tok == succTag then some (Code.succ :: stk)
      else bif tok == leftTag then some (Code.left :: stk)
      else bif tok == rightTag then some (Code.right :: stk)
      else bif tok == rfindTag then
        parseUnaryStack Code.rfind' stk
      else bif tok == pairTag then
        parseBinaryStack Code.pair stk
      else bif tok == compTag then
        parseBinaryStack Code.comp stk
      else bif tok == precTag then
        parseBinaryStack Code.prec stk
      else none

private def parseTokensReverse (toksRev : List Nat) : Option (List Code) :=
  toksRev.foldl stepParseRev (some [])

private def parsedAdditiveProgram (n : Nat) : Option (List Code) :=
  Option.bind (tokenizeReverse (BitString.ofNatExact n)) parseTokensReverse

private def singletonListCodeOrZero (stk : List Code) : Code :=
  Option.getD
    (Option.bind stk.head? fun c =>
      bif stk.tail.length == 0 then some c else none)
    Code.zero

private def singletonCodeOrZero : Option (List Code) → Code
  | some stk => singletonListCodeOrZero stk
  | _ => Code.zero

/-- Decode a natural payload according to `additiveCodeToProgram`. -/
def decodeAdditiveProgramNat (n : Nat) : Code :=
  singletonCodeOrZero (parsedAdditiveProgram n)

/-- Decode a bitstring according to `additiveCodeToProgram`. -/
def additiveProgramToCode (p : Program) : Code :=
  decodeAdditiveProgramNat (BitString.toNatExact p)

private theorem decodeTagNat_primrec : Primrec decodeTagNat := by
  simpa [decodeTagNat] using
    (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const zeroTag))
      (Primrec.const (some zeroTag))
      (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const succTag))
        (Primrec.const (some succTag))
        (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const leftTag))
          (Primrec.const (some leftTag))
          (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const rightTag))
            (Primrec.const (some rightTag))
            (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const pairTag))
              (Primrec.const (some pairTag))
              (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const compTag))
                (Primrec.const (some compTag))
                (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const precTag))
                  (Primrec.const (some precTag))
                  (Primrec.cond (Primrec.beq.comp Primrec.id (Primrec.const rfindTag))
                    (Primrec.const (some rfindTag))
                    (Primrec.const none)))))))))

private theorem stepTokenize_primrec : Primrec₂ stepTokenize := by
  let hPending : Primrec fun p : TokenizeState × Bool => p.1.1 ++ [p.2] :=
    Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  let hPendingSome : Primrec fun q : (TokenizeState × Bool) × List Nat =>
      q.1.1.1 ++ [q.1.2] :=
    Primrec.list_concat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  let hDecode : Primrec fun q : (TokenizeState × Bool) × List Nat =>
      decodeTagNat (BitString.toNatExact (q.1.1.1 ++ [q.1.2])) :=
    decodeTagNat_primrec.comp (BitString.toNatExact_primrec.comp hPendingSome)
  let hMap : Primrec fun q : (TokenizeState × Bool) × List Nat =>
      (decodeTagNat (BitString.toNatExact (q.1.1.1 ++ [q.1.2]))).map
        (fun tok => tok :: q.2) :=
    Primrec.option_map hDecode
      ((Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂)
  let hDone : Primrec fun q : (TokenizeState × Bool) × List Nat =>
      (([] : Program),
        (decodeTagNat (BitString.toNatExact (q.1.1.1 ++ [q.1.2]))).map
          (fun tok => tok :: q.2)) := by
    exact (Primrec.pair (Primrec.const ([] : Program)) hMap).of_eq fun _ => rfl
  let hKeep : Primrec fun q : (TokenizeState × Bool) × List Nat =>
      ((q.1.1.1 ++ [q.1.2]), some q.2) := by
    exact (Primrec.pair hPendingSome (Primrec.option_some.comp Primrec.snd)).of_eq fun _ => rfl
  let hCond : Primrec fun q : (TokenizeState × Bool) × List Nat =>
      BitString.blen (q.1.1.1 ++ [q.1.2]) == 4 :=
    Primrec.beq.comp (Primrec.list_length.comp hPendingSome) (Primrec.const 4)
  let someTokenizeBody :
      Primrec fun q : (TokenizeState × Bool) × List Nat =>
        let pending := q.1.1.1 ++ [q.1.2]
        bif BitString.blen pending == 4 then
          ([], (decodeTagNat (BitString.toNatExact pending)).map fun tok => tok :: q.2)
        else
          (pending, some q.2) :=
    (Primrec.cond hCond hDone hKeep).of_eq fun q => by
      simp
  let hSome :
      Primrec₂ fun p : TokenizeState × Bool =>
        fun toks : List Nat =>
          let pending := p.1.1 ++ [p.2]
          bif BitString.blen pending == 4 then
            ([], (decodeTagNat (BitString.toNatExact pending)).map fun tok => tok :: toks)
          else
            (pending, some toks) :=
    someTokenizeBody.to₂
  exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst) Primrec.fst hSome).to₂.of_eq
    fun st b => by
      cases st with
      | mk pref opt =>
          cases opt <;> rfl

private theorem tokenizeReverse_primrec : Primrec tokenizeReverse := by
  let foldTokenize : Program → TokenizeState :=
    fun p => p.foldl stepTokenize ([], some [])
  let hStep :
      Primrec₂ fun _ : Program =>
        fun sb : TokenizeState × Bool => stepTokenize sb.1 sb.2 :=
    (stepTokenize_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  let hFold : Primrec foldTokenize :=
    (Primrec.list_foldl Primrec.id (Primrec.const (([], some []) : TokenizeState)) hStep).of_eq
      fun _ => rfl
  let emptyPrefix : Program → Bool := fun p => foldTokenize p |>.1.length == 0
  let hCond : Primrec emptyPrefix := by
    exact Primrec.beq.comp
      (Primrec.list_length.comp (Primrec.fst.comp hFold))
      (Primrec.const 0)
  exact (Primrec.cond hCond (Primrec.snd.comp hFold) (Primrec.const none)).of_eq
    fun p => by
      cases h : foldTokenize p with
      | mk pref toks =>
          cases pref <;> simp [tokenizeReverse, foldTokenize, emptyPrefix, h]

private theorem parseUnaryStack_primrec {mk : Code → Code} (hmk : Primrec mk) :
    Primrec (parseUnaryStack mk) := by
  unfold parseUnaryStack
  exact Primrec.option_bind Primrec.list_head?
    ((Primrec.option_some.comp
      (Primrec.list_cons.comp (hmk.comp Primrec.snd) (Primrec.list_tail.comp Primrec.fst))).to₂)

private theorem parseBinaryStack_primrec {mk : Code → Code → Code} (hmk : Primrec₂ mk) :
    Primrec (parseBinaryStack mk) := by
  unfold parseBinaryStack
  refine Primrec.option_bind Primrec.list_head? ?_
  let hHead₂ : Primrec fun p : List Code × Code => (List.tail p.1).head? :=
    Primrec.list_head?.comp (Primrec.list_tail.comp Primrec.fst)
  let hSome :
      Primrec₂ fun p : List Code × Code =>
        fun cg : Code => some (mk p.2 cg :: p.1.tail.tail) :=
    (Primrec.option_some.comp
      (Primrec.list_cons.comp
        (hmk.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.list_tail.comp (Primrec.list_tail.comp (Primrec.fst.comp Primrec.fst))))).to₂
  exact (Primrec.option_bind hHead₂ hSome).to₂

private theorem stepParseRev_primrec : Primrec₂ stepParseRev := by
  let hTok : Primrec fun q : (Option (List Code) × Nat) × List Code => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  let hZero : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      some (Code.zero :: q.2) :=
    (Primrec.option_some.comp
      (Primrec.list_cons.comp (Primrec.const Code.zero) Primrec.snd)).of_eq fun _ => rfl
  let hSucc : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      some (Code.succ :: q.2) :=
    (Primrec.option_some.comp
      (Primrec.list_cons.comp (Primrec.const Code.succ) Primrec.snd)).of_eq fun _ => rfl
  let hLeft : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      some (Code.left :: q.2) :=
    (Primrec.option_some.comp
      (Primrec.list_cons.comp (Primrec.const Code.left) Primrec.snd)).of_eq fun _ => rfl
  let hRight : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      some (Code.right :: q.2) :=
    (Primrec.option_some.comp
      (Primrec.list_cons.comp (Primrec.const Code.right) Primrec.snd)).of_eq fun _ => rfl
  let hRfind : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      parseUnaryStack Code.rfind' q.2 :=
    (parseUnaryStack_primrec Nat.Partrec.Code.primrec_rfind').comp Primrec.snd
  let hPair : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      parseBinaryStack Code.pair q.2 :=
    (parseBinaryStack_primrec Nat.Partrec.Code.primrec₂_pair).comp Primrec.snd
  let hComp : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      parseBinaryStack Code.comp q.2 :=
    (parseBinaryStack_primrec Nat.Partrec.Code.primrec₂_comp).comp Primrec.snd
  let hPrec : Primrec fun q : (Option (List Code) × Nat) × List Code =>
      parseBinaryStack Code.prec q.2 :=
    (parseBinaryStack_primrec Nat.Partrec.Code.primrec₂_prec).comp Primrec.snd
  let hTail₁ :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == precTag then parseBinaryStack Code.prec q.2 else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const precTag)) hPrec
      (Primrec.const none)).of_eq fun q => by
      simp
  let hTail₂ :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == compTag then parseBinaryStack Code.comp q.2
        else bif q.1.2 == precTag then parseBinaryStack Code.prec q.2
        else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const compTag)) hComp hTail₁).of_eq fun q => by
      simp
  let hTail₃ :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == pairTag then parseBinaryStack Code.pair q.2
        else bif q.1.2 == compTag then parseBinaryStack Code.comp q.2
        else bif q.1.2 == precTag then parseBinaryStack Code.prec q.2
        else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const pairTag)) hPair hTail₂).of_eq fun q => by
      simp
  let hTail₄ :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == rfindTag then parseUnaryStack Code.rfind' q.2
        else bif q.1.2 == pairTag then parseBinaryStack Code.pair q.2
        else bif q.1.2 == compTag then parseBinaryStack Code.comp q.2
        else bif q.1.2 == precTag then parseBinaryStack Code.prec q.2
        else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const rfindTag)) hRfind hTail₃).of_eq fun q => by
      simp
  let hTail₅ :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == rightTag then some (Code.right :: q.2)
        else bif q.1.2 == rfindTag then parseUnaryStack Code.rfind' q.2
        else bif q.1.2 == pairTag then parseBinaryStack Code.pair q.2
        else bif q.1.2 == compTag then parseBinaryStack Code.comp q.2
        else bif q.1.2 == precTag then parseBinaryStack Code.prec q.2
        else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const rightTag)) hRight hTail₄).of_eq fun q => by
      simp
  let hTail₆ :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == leftTag then some (Code.left :: q.2)
        else bif q.1.2 == rightTag then some (Code.right :: q.2)
        else bif q.1.2 == rfindTag then parseUnaryStack Code.rfind' q.2
        else bif q.1.2 == pairTag then parseBinaryStack Code.pair q.2
        else bif q.1.2 == compTag then parseBinaryStack Code.comp q.2
        else bif q.1.2 == precTag then parseBinaryStack Code.prec q.2
        else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const leftTag)) hLeft hTail₅).of_eq fun q => by
      simp
  let hTail₇ :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == succTag then some (Code.succ :: q.2)
        else bif q.1.2 == leftTag then some (Code.left :: q.2)
        else bif q.1.2 == rightTag then some (Code.right :: q.2)
        else bif q.1.2 == rfindTag then parseUnaryStack Code.rfind' q.2
        else bif q.1.2 == pairTag then parseBinaryStack Code.pair q.2
        else bif q.1.2 == compTag then parseBinaryStack Code.comp q.2
        else bif q.1.2 == precTag then parseBinaryStack Code.prec q.2
        else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const succTag)) hSucc hTail₆).of_eq fun q => by
      simp
  let someParseBody :
      Primrec fun q : (Option (List Code) × Nat) × List Code =>
        bif q.1.2 == zeroTag then some (Code.zero :: q.2)
        else bif q.1.2 == succTag then some (Code.succ :: q.2)
        else bif q.1.2 == leftTag then some (Code.left :: q.2)
        else bif q.1.2 == rightTag then some (Code.right :: q.2)
        else bif q.1.2 == rfindTag then parseUnaryStack Code.rfind' q.2
        else bif q.1.2 == pairTag then parseBinaryStack Code.pair q.2
        else bif q.1.2 == compTag then parseBinaryStack Code.comp q.2
        else bif q.1.2 == precTag then parseBinaryStack Code.prec q.2
        else none :=
    (Primrec.cond (Primrec.beq.comp hTok (Primrec.const zeroTag)) hZero hTail₇).of_eq fun q => by
      simp
  let hSome :
      Primrec₂ fun p : Option (List Code) × Nat =>
        fun stk : List Code =>
          bif p.2 == zeroTag then some (Code.zero :: stk)
          else bif p.2 == succTag then some (Code.succ :: stk)
          else bif p.2 == leftTag then some (Code.left :: stk)
          else bif p.2 == rightTag then some (Code.right :: stk)
          else bif p.2 == rfindTag then parseUnaryStack Code.rfind' stk
          else bif p.2 == pairTag then parseBinaryStack Code.pair stk
          else bif p.2 == compTag then parseBinaryStack Code.comp stk
          else bif p.2 == precTag then parseBinaryStack Code.prec stk
          else none :=
    someParseBody.to₂
  exact (Primrec.option_casesOn Primrec.fst (Primrec.const none) hSome).to₂.of_eq
    fun stk tok => by
      cases stk <;> rfl

private theorem parseTokensReverse_primrec : Primrec parseTokensReverse := by
  let foldParse : List Nat → Option (List Code) :=
    fun toksRev => toksRev.foldl stepParseRev (some [])
  let hStep :
      Primrec₂ fun _ : List Nat =>
        fun sb : Option (List Code) × Nat => stepParseRev sb.1 sb.2 :=
    (stepParseRev_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldl
      Primrec.id
      (Primrec.const (some ([] : List Code) : Option (List Code)))
      hStep).of_eq fun toksRev => by
        simp [foldParse, parseTokensReverse]

private theorem singletonListCodeOrZero_primrec : Primrec singletonListCodeOrZero := by
  unfold singletonListCodeOrZero
  let hHead : Primrec fun stk : List Code => stk.head? := Primrec.list_head?
  let hSomeBody :
      Primrec fun q : List Code × Code => bif q.1.tail.length == 0 then some q.2 else none :=
    (Primrec.cond
      (Primrec.beq.comp
        (Primrec.list_length.comp (Primrec.list_tail.comp Primrec.fst))
        (Primrec.const 0))
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none))
  let hSome :
      Primrec₂ fun stk : List Code =>
        fun c : Code => bif stk.tail.length == 0 then some c else none :=
    hSomeBody.to₂
  exact Primrec.option_getD.comp
    (Primrec.option_bind hHead hSome)
    (Primrec.const Code.zero)

private theorem singletonCodeOrZero_primrec : Primrec singletonCodeOrZero := by
  unfold singletonCodeOrZero
  exact (Primrec.option_casesOn Primrec.id
    (Primrec.const Code.zero)
    ((singletonListCodeOrZero_primrec.comp Primrec.snd).to₂)).of_eq fun o => by
      cases o <;> rfl

theorem decodeAdditiveProgramNat_primrec : Primrec decodeAdditiveProgramNat := by
  have hParsed : Primrec parsedAdditiveProgram := by
    unfold parsedAdditiveProgram
    exact Primrec.option_bind
      (tokenizeReverse_primrec.comp BitString.ofNatExact_primrec)
      (parseTokensReverse_primrec.comp Primrec.snd).to₂
  exact singletonCodeOrZero_primrec.comp hParsed

theorem decodeAdditiveProgramNat_computable : Computable decodeAdditiveProgramNat :=
  decodeAdditiveProgramNat_primrec.to_comp

@[simp] private theorem toNatExact_zeroBits : BitString.toNatExact zeroBits = zeroTag := by
  simp [zeroBits, zeroTag, BitString.toNatExact]

@[simp] private theorem toNatExact_succBits : BitString.toNatExact succBits = succTag := by
  simp [succBits, succTag, BitString.toNatExact]

@[simp] private theorem toNatExact_leftBits : BitString.toNatExact leftBits = leftTag := by
  simp [leftBits, leftTag, BitString.toNatExact]

@[simp] private theorem toNatExact_rightBits : BitString.toNatExact rightBits = rightTag := by
  simp [rightBits, rightTag, BitString.toNatExact]

@[simp] private theorem toNatExact_pairBits : BitString.toNatExact pairBits = pairTag := by
  simp [pairBits, pairTag, BitString.toNatExact]

@[simp] private theorem toNatExact_compBits : BitString.toNatExact compBits = compTag := by
  simp [compBits, compTag, BitString.toNatExact]

@[simp] private theorem toNatExact_precBits : BitString.toNatExact precBits = precTag := by
  simp [precBits, precTag, BitString.toNatExact]

@[simp] private theorem toNatExact_rfindBits : BitString.toNatExact rfindBits = rfindTag := by
  simp [rfindBits, rfindTag, BitString.toNatExact]

private theorem tokenizeReverse_additiveCodeToProgram_aux (c : Code) (toks : List Nat) :
    List.foldl stepTokenize ([], some toks) (additiveCodeToProgram c) =
      ([], some (encodeTokensRev c ++ toks)) := by
  induction c generalizing toks with
  | zero =>
      rw [additiveCodeToProgram]
      simp [stepTokenize, zeroBits, encodeTokensRev, decodeTagNat, zeroTag, BitString.toNatExact]
  | succ =>
      rw [additiveCodeToProgram]
      simp [stepTokenize, succBits, encodeTokensRev, decodeTagNat, zeroTag, succTag,
        BitString.toNatExact]
  | left =>
      rw [additiveCodeToProgram]
      simp [stepTokenize, leftBits, encodeTokensRev, decodeTagNat, zeroTag, succTag, leftTag,
        BitString.toNatExact]
  | right =>
      rw [additiveCodeToProgram]
      simp [stepTokenize, rightBits, encodeTokensRev, decodeTagNat, zeroTag, succTag, leftTag,
        rightTag, BitString.toNatExact]
  | pair cf cg ihf ihg =>
      rw [additiveCodeToProgram, List.foldl_append, List.foldl_append]
      have htag : List.foldl stepTokenize ([], some toks) pairBits = ([], some (pairTag :: toks)) := by
        simp [stepTokenize, pairBits, zeroTag, succTag, leftTag, rightTag, pairTag, decodeTagNat,
          BitString.toNatExact]
      rw [htag, ihf (pairTag :: toks), ihg (encodeTokensRev cf ++ pairTag :: toks)]
      simp [encodeTokensRev, List.append_assoc]
  | comp cf cg ihf ihg =>
      rw [additiveCodeToProgram, List.foldl_append, List.foldl_append]
      have htag : List.foldl stepTokenize ([], some toks) compBits = ([], some (compTag :: toks)) := by
        simp [stepTokenize, compBits, zeroTag, succTag, leftTag, rightTag, pairTag, compTag,
          decodeTagNat, BitString.toNatExact]
      rw [htag, ihf (compTag :: toks), ihg (encodeTokensRev cf ++ compTag :: toks)]
      simp [encodeTokensRev, List.append_assoc]
  | prec cf cg ihf ihg =>
      rw [additiveCodeToProgram, List.foldl_append, List.foldl_append]
      have htag : List.foldl stepTokenize ([], some toks) precBits = ([], some (precTag :: toks)) := by
        simp [stepTokenize, precBits, zeroTag, succTag, leftTag, rightTag, pairTag, compTag,
          precTag, decodeTagNat, BitString.toNatExact]
      rw [htag, ihf (precTag :: toks), ihg (encodeTokensRev cf ++ precTag :: toks)]
      simp [encodeTokensRev, List.append_assoc]
  | rfind' cf ih =>
      rw [additiveCodeToProgram, List.foldl_append]
      have htag : List.foldl stepTokenize ([], some toks) rfindBits = ([], some (rfindTag :: toks)) := by
        simp [stepTokenize, rfindBits, zeroTag, succTag, leftTag, rightTag, pairTag, compTag,
          precTag, rfindTag, decodeTagNat, BitString.toNatExact]
      rw [htag, ih (rfindTag :: toks)]
      simp [encodeTokensRev, List.append_assoc]

private theorem parseTokensReverse_encodeTokensRev_aux (c : Code) (stk : List Code) :
    List.foldl stepParseRev (some stk) (encodeTokensRev c) = some (c :: stk) := by
  induction c generalizing stk with
  | zero =>
      simp [encodeTokensRev, stepParseRev, zeroTag]
  | succ =>
      simp [encodeTokensRev, stepParseRev, zeroTag, succTag]
  | left =>
      simp [encodeTokensRev, stepParseRev, zeroTag, succTag, leftTag]
  | right =>
      simp [encodeTokensRev, stepParseRev, zeroTag, succTag, leftTag, rightTag]
  | pair cf cg ihf ihg =>
      rw [encodeTokensRev, List.foldl_append, List.foldl_append, ihg stk, ihf (cg :: stk)]
      simp [stepParseRev, parseBinaryStack, zeroTag, succTag, leftTag, rightTag, pairTag, rfindTag]
  | comp cf cg ihf ihg =>
      rw [encodeTokensRev, List.foldl_append, List.foldl_append, ihg stk, ihf (cg :: stk)]
      simp [stepParseRev, parseBinaryStack, zeroTag, succTag, leftTag, rightTag, pairTag, compTag,
        rfindTag]
  | prec cf cg ihf ihg =>
      rw [encodeTokensRev, List.foldl_append, List.foldl_append, ihg stk, ihf (cg :: stk)]
      simp [stepParseRev, parseBinaryStack, zeroTag, succTag, leftTag, rightTag, pairTag, compTag,
        precTag, rfindTag]
  | rfind' cf ih =>
      rw [encodeTokensRev, List.foldl_append, ih stk]
      simp [stepParseRev, parseUnaryStack, zeroTag, succTag, leftTag, rightTag, pairTag, compTag,
        precTag, rfindTag]

@[simp] theorem decodeAdditiveProgramNat_additiveCodeToProgram (c : Code) :
    decodeAdditiveProgramNat (BitString.toNatExact (additiveCodeToProgram c)) = c := by
  have htok : tokenizeReverse (additiveCodeToProgram c) = some (encodeTokensRev c) := by
    unfold tokenizeReverse
    rw [tokenizeReverse_additiveCodeToProgram_aux c []]
    simp
  have hparse : parseTokensReverse (encodeTokensRev c) = some [c] := by
    unfold parseTokensReverse
    simpa using parseTokensReverse_encodeTokensRev_aux c []
  unfold decodeAdditiveProgramNat parsedAdditiveProgram singletonCodeOrZero singletonListCodeOrZero
  simp [BitString.ofNatExact_toNatExact, htok, hparse]

@[simp] theorem additiveProgramToCode_additiveCodeToProgram (c : Code) :
    additiveProgramToCode (additiveCodeToProgram c) = c := by
  unfold additiveProgramToCode
  simpa using decodeAdditiveProgramNat_additiveCodeToProgram c

end UniversalMachine

end IcTheory
