import IcTheory.Basics.Pairing
import Mathlib.Data.List.TakeDrop

namespace IcTheory

namespace BitString

/-- An internal self-delimiting length code based on the exact bitstring bridge. -/
def exactLengthCode (x : BitString) : BitString :=
  e1 (ofNatExact (blen x))

/-- An internal pair encoding with additive length
`|x| + |y| + O(log |x|)`.
This is not the paper's public pairing; it is a machine-facing payload format. -/
def exactPairPayload (x y : BitString) : BitString :=
  exactLengthCode x ++ x ++ y

/-- Nested exact payload used to package four machine components. -/
def exactQuadPayload (a b c d : BitString) : BitString :=
  exactPairPayload (exactPairPayload a b) (exactPairPayload c d)

@[simp] theorem blen_exactLengthCode (x : BitString) :
    blen (exactLengthCode x) = 2 * blen (ofNatExact (blen x)) + 1 := by
  simp [exactLengthCode]

@[simp] theorem blen_exactPairPayload (x y : BitString) :
    blen (exactPairPayload x y) =
      blen x + blen y + (2 * blen (ofNatExact (blen x)) + 1) := by
  simp [exactPairPayload, exactLengthCode, Nat.add_assoc, Nat.add_comm]

theorem blen_exactPairPayload_le_prefixProgram (r f : BitString) :
    blen (exactPairPayload r f) ≤ blen (BitString.pair f (BitString.e2 r)) := by
  rw [blen_exactPairPayload, blen_pair, blen_e2]
  have henc : blen (ofNatExact (blen r)) ≤ blen (ofNat (blen r)) :=
    blen_ofNatExact_le_ofNat (blen r)
  omega

@[simp] theorem blen_exactQuadPayload (a b c d : BitString) :
    blen (exactQuadPayload a b c d) =
      blen (exactPairPayload a b) + blen (exactPairPayload c d) +
        (2 * blen (ofNatExact (blen (exactPairPayload a b))) + 1) := by
  simp [exactQuadPayload, blen_exactPairPayload, Nat.add_assoc, Nat.add_comm]

theorem blen_exactQuadPayload_le_twoPrefixPrograms (r₁ f₁ r₂ f₂ : BitString) :
    blen (exactQuadPayload r₁ f₁ r₂ f₂) ≤
      blen (BitString.pair f₁ (BitString.e2 r₁)) +
        blen (BitString.pair f₂ (BitString.e2 r₂)) +
        (2 * blen (BitString.ofNat (blen (BitString.pair f₁ (BitString.e2 r₁)))) + 1) := by
  rw [blen_exactQuadPayload]
  let p₁ := BitString.pair f₁ (BitString.e2 r₁)
  let q₁ := exactPairPayload r₁ f₁
  have hq₁ : blen q₁ ≤ blen p₁ := by
    simpa [p₁, q₁] using blen_exactPairPayload_le_prefixProgram r₁ f₁
  have hq₂ : blen (exactPairPayload r₂ f₂) ≤ blen (BitString.pair f₂ (BitString.e2 r₂)) := by
    simpa using blen_exactPairPayload_le_prefixProgram r₂ f₂
  have henc :
      blen (ofNatExact (blen q₁)) ≤ blen (ofNat (blen p₁)) := by
    exact le_trans (blen_ofNatExact_le_ofNat (blen q₁)) (blen_ofNat_mono hq₁)
  dsimp [p₁, q₁] at hq₁ henc ⊢
  omega

/-- Count the initial run of `true` bits. -/
def countLeadingTrue : BitString → Nat
  | true :: xs => countLeadingTrue xs + 1
  | _ => 0

/-- Split a bitstring after `n` many bits. -/
def splitAt : Nat → BitString → BitString × BitString
  | 0, xs => ([], xs)
  | _ + 1, [] => ([], [])
  | n + 1, x :: xs =>
      let ys := splitAt n xs
      (x :: ys.1, ys.2)

@[simp] theorem countLeadingTrue_nil : countLeadingTrue ([] : BitString) = 0 := rfl

@[simp] theorem countLeadingTrue_false (xs : BitString) :
    countLeadingTrue (false :: xs) = 0 := rfl

@[simp] theorem countLeadingTrue_true (xs : BitString) :
    countLeadingTrue (true :: xs) = countLeadingTrue xs + 1 := rfl

theorem countLeadingTrue_primrec : Primrec countLeadingTrue := by
  have hstep : Primrec₂ fun (_ : List Bool) (p : Bool × Nat) => cond p.1 (p.2 + 1) 0 := by
    refine Primrec.cond (hc := ?_) (hf := ?_) (hg := ?_)
    · exact Primrec.fst.comp Primrec.snd
    · exact Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
    · exact Primrec.const 0
  refine (Primrec.list_foldr (hf := Primrec.id) (hg := Primrec.const 0) hstep).of_eq ?_
  intro xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b <;> simpa [countLeadingTrue] using ih

theorem countLeadingTrue_computable : Computable countLeadingTrue :=
  countLeadingTrue_primrec.to_comp

@[simp] theorem splitAt_zero (xs : BitString) : splitAt 0 xs = ([], xs) := rfl

@[simp] theorem splitAt_nil (n : Nat) : splitAt (n + 1) ([] : BitString) = ([], []) := rfl

@[simp] theorem splitAt_cons (n : Nat) (x : Bool) (xs : BitString) :
    splitAt (n + 1) (x :: xs) = (x :: (splitAt n xs).1, (splitAt n xs).2) := rfl

theorem splitAt_eq_take_drop : ∀ n : Nat, ∀ xs : BitString,
    splitAt n xs = (xs.take n, xs.drop n)
  | 0, xs => by simp [splitAt]
  | n + 1, [] => by simp [splitAt]
  | n + 1, x :: xs => by
      simp [splitAt, splitAt_eq_take_drop n xs]

private def splitAdvance (state : BitString × BitString) : BitString × BitString :=
  match state.2 with
  | [] => (state.1, [])
  | b :: suff => (state.1.concat b, suff)

private theorem splitAdvance_primrec : Primrec splitAdvance := by
  let A := BitString × BitString
  have hnil : Primrec (fun a : A => (a.1, ([] : BitString))) := by
    exact (Primrec.pair Primrec.fst (Primrec.const ([] : BitString))).of_eq fun _ => rfl
  have hbool : Primrec fun p : A × (Bool × BitString) => (p.2.1 : Bool) := by
    exact Primrec.fst.comp Primrec.snd
  have hh1' : Primrec fun p : A × (Bool × BitString) => p.1.1 ++ [p.2.1] := by
    exact Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) hbool
  have hh1 : Primrec fun p : A × (Bool × BitString) => p.1.1.concat (p.2.1 : Bool) := by
    exact hh1'.of_eq fun p => by simp
  have hh2 : Primrec fun p : A × (Bool × BitString) => (p.2.2 : BitString) := by
    exact Primrec.snd.comp Primrec.snd
  have hcons : Primrec₂ fun (a : A) (q : Bool × BitString) => (a.1.concat q.1, q.2) := by
    exact ((Primrec.pair hh1 hh2).to₂).of_eq fun a q => rfl
  refine (Primrec.list_casesOn (f := fun a : A => a.2) Primrec.snd hnil hcons).of_eq ?_
  rintro ⟨pref, suff⟩
  cases suff <;> simp [splitAdvance]

private theorem splitAt_step (xs : BitString) (n : Nat) :
    splitAdvance (splitAt n xs) = splitAt (n + 1) xs := by
  rw [splitAt_eq_take_drop, splitAt_eq_take_drop]
  cases hdrop : xs.drop n with
  | nil =>
      have hzero : 0 = xs.length - n := by
        simpa [hdrop] using (List.length_drop (i := n) (l := xs))
      have hlen : xs.length ≤ n := by omega
      simp [splitAdvance, List.take_of_length_le hlen,
        List.take_of_length_le (Nat.le_trans hlen (Nat.le_succ _)),
        List.drop_eq_nil_of_le (Nat.le_trans hlen (Nat.le_succ _))]
  | cons b suff =>
      have hlt : n < xs.length := by
        apply lt_of_not_ge
        intro hge
        rw [List.drop_eq_nil_of_le hge] at hdrop
        simp at hdrop
      have hdrop' : xs.drop n = xs[n] :: xs.drop (n + 1) := List.drop_eq_getElem_cons hlt
      have hcons : xs[n] :: xs.drop (n + 1) = b :: suff := by
        simpa [hdrop] using hdrop'
      have hb : xs[n] = b := by
        injection hcons with hb hs
      have hsuff : xs.drop (n + 1) = suff := by
        injection hcons with hb hs
      simp [splitAdvance, hsuff, List.concat_eq_append]
      simpa [hb] using (List.take_concat_get' xs n hlt)

theorem splitAt_primrec : Primrec₂ splitAt := by
  have hinit : Primrec (fun p : Nat × BitString => (([] : BitString), p.2)) := by
    exact (Primrec.pair (Primrec.const ([] : BitString)) Primrec.snd).of_eq fun _ => rfl
  have hiter : Primrec₂ fun n xs => (splitAdvance^[n]) (([] : BitString), xs) := by
    simpa using
      ((Primrec.nat_iterate (f := fun p : Nat × BitString => p.1)
        (g := fun p : Nat × BitString => (([] : BitString), p.2))
        (h := fun (_ : Nat × BitString) s => splitAdvance s)
        Primrec.fst hinit ((splitAdvance_primrec.comp Primrec.snd).to₂)).to₂)
  have hEq : ∀ n xs, (splitAdvance^[n]) (([] : BitString), xs) = splitAt n xs := by
    intro n xs
    induction n with
    | zero => simp [splitAt]
    | succ n ih =>
        simpa [Function.iterate_succ_apply', ih] using splitAt_step xs n
  exact hiter.of_eq hEq

theorem splitAt_computable : Computable₂ splitAt :=
  splitAt_primrec.to_comp

@[simp] theorem countLeadingTrue_unary (n : Nat) :
    countLeadingTrue (unary n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [unary, Computability.unaryEncodeNat, ih]

@[simp] theorem countLeadingTrue_unaryHeader (n : Nat) (xs : BitString) :
    countLeadingTrue (unaryHeader n ++ xs) = n := by
  induction n with
  | zero =>
      simp [unaryHeader, unary, Computability.unaryEncodeNat]
  | succ n ih =>
      simpa [unaryHeader, unary, Computability.unaryEncodeNat, countLeadingTrue] using
        congrArg Nat.succ ih

/-- Decode the internal pair payload by reading the exact length code and then splitting
off that many bits. -/
def decodeExactPairPayload (payload : BitString) : BitString × BitString :=
  let lenCodeBits := countLeadingTrue payload
  let rest₁ := (splitAt (lenCodeBits + 1) payload).2
  let lenCode := (splitAt lenCodeBits rest₁).1
  let rest₂ := (splitAt lenCodeBits rest₁).2
  splitAt (toNatExact lenCode) rest₂

/-- Decode the nested four-component payload used for joint-description composition. -/
def decodeExactQuadPayload (payload : BitString) : BitString × BitString × BitString × BitString :=
  let ab_cd := decodeExactPairPayload payload
  let ab := decodeExactPairPayload ab_cd.1
  let cd := decodeExactPairPayload ab_cd.2
  (ab.1, ab.2, cd.1, cd.2)

theorem decodeExactPairPayload_primrec : Primrec decodeExactPairPayload := by
  have hSplitHeader :
      Primrec fun payload => splitAt (countLeadingTrue payload + 1) payload := by
    exact splitAt_primrec.comp
      (Primrec.nat_add.comp countLeadingTrue_primrec (Primrec.const 1))
      Primrec.id
  have hRest₁ :
      Primrec fun payload => (splitAt (countLeadingTrue payload + 1) payload).2 := by
    exact Primrec.snd.comp hSplitHeader
  have hSplitLen :
      Primrec fun payload => splitAt (countLeadingTrue payload) ((splitAt (countLeadingTrue payload + 1) payload).2) := by
    exact splitAt_primrec.comp countLeadingTrue_primrec hRest₁
  have hLenCode :
      Primrec fun payload => (splitAt (countLeadingTrue payload) ((splitAt (countLeadingTrue payload + 1) payload).2)).1 := by
    exact Primrec.fst.comp hSplitLen
  have hRest₂ :
      Primrec fun payload => (splitAt (countLeadingTrue payload) ((splitAt (countLeadingTrue payload + 1) payload).2)).2 := by
    exact Primrec.snd.comp hSplitLen
  exact (splitAt_primrec.comp (BitString.toNatExact_primrec.comp hLenCode) hRest₂).of_eq
    fun payload => by rfl

theorem decodeExactPairPayload_computable : Computable decodeExactPairPayload :=
  decodeExactPairPayload_primrec.to_comp

theorem decodeExactQuadPayload_primrec : Primrec decodeExactQuadPayload := by
  refine (Primrec.pair
      (Primrec.fst.comp
        (decodeExactPairPayload_primrec.comp
          (Primrec.fst.comp (decodeExactPairPayload_primrec.comp Primrec.id))))
      (Primrec.pair
        (Primrec.snd.comp
          (decodeExactPairPayload_primrec.comp
            (Primrec.fst.comp (decodeExactPairPayload_primrec.comp Primrec.id))))
        (Primrec.pair
          (Primrec.fst.comp
            (decodeExactPairPayload_primrec.comp
              (Primrec.snd.comp (decodeExactPairPayload_primrec.comp Primrec.id))))
          (Primrec.snd.comp
            (decodeExactPairPayload_primrec.comp
              (Primrec.snd.comp (decodeExactPairPayload_primrec.comp Primrec.id))))))).of_eq ?_
  intro payload
  rfl

theorem decodeExactQuadPayload_computable : Computable decodeExactQuadPayload :=
  decodeExactQuadPayload_primrec.to_comp

@[simp] theorem decodeExactPairPayload_exactPairPayload (x y : BitString) :
    decodeExactPairPayload (exactPairPayload x y) = (x, y) := by
  let k := blen (ofNatExact (blen x))
  have hk : countLeadingTrue (e1 (ofNatExact (blen x)) ++ x ++ y) = k := by
    simpa [k, e1, unaryHeader, Nat.add_assoc] using
      (countLeadingTrue_unaryHeader k ((ofNatExact (blen x)) ++ x ++ y))
  have hsplit₁ :
      splitAt (k + 1) (e1 (ofNatExact (blen x)) ++ x ++ y) =
        (unaryHeader k, ofNatExact (blen x) ++ x ++ y) := by
    simpa [k, e1, splitAt_eq_take_drop]
      using (splitAt_eq_take_drop (k + 1) (e1 (ofNatExact (blen x)) ++ x ++ y))
  have hsplit₂ :
      splitAt k (ofNatExact (blen x) ++ x ++ y) = (ofNatExact (blen x), x ++ y) := by
    simpa [k, splitAt_eq_take_drop]
      using (splitAt_eq_take_drop k (ofNatExact (blen x) ++ x ++ y))
  have hrest₁ :
      (splitAt (k + 1) (e1 (ofNatExact (blen x)) ++ x ++ y)).2 =
        ofNatExact (blen x) ++ x ++ y := by
    simpa using congrArg Prod.snd hsplit₁
  have hlenCode :
      (splitAt k (ofNatExact (blen x) ++ x ++ y)).1 = ofNatExact (blen x) := by
    simpa using congrArg Prod.fst hsplit₂
  have hrest₂ :
      (splitAt k (ofNatExact (blen x) ++ x ++ y)).2 = x ++ y := by
    simpa using congrArg Prod.snd hsplit₂
  simp_rw [decodeExactPairPayload, exactPairPayload, exactLengthCode]
  simp_rw [hk]
  simp_rw [hrest₁]
  simp_rw [hlenCode]
  simp_rw [hrest₂]
  rw [toNatExact_ofNatExact, splitAt_eq_take_drop]
  simp

@[simp] theorem decodeExactQuadPayload_exactQuadPayload (a b c d : BitString) :
    decodeExactQuadPayload (exactQuadPayload a b c d) = (a, b, c, d) := by
  simp [decodeExactQuadPayload, exactQuadPayload]

end BitString

end IcTheory
