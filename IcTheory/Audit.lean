import IcTheory

open IcTheory Compression

/-!
Run this file with:

```bash
lake env lean IcTheory/Audit.lean
```

`#check` prints the theorem statement actually proved in Lean.
`#print axioms` prints the kernel-reported axioms used by that theorem.

For the main paper theorems in this repository, the expected axiom report is the standard
classical trio `[propext, Classical.choice, Quot.sound]`, with no project-local axioms.
-/

-- Section 3
#check Compression.theorem31
#print axioms Compression.theorem31

#check Compression.theorem32
#print axioms Compression.theorem32

#check Compression.theorem33_eq16
#print axioms Compression.theorem33_eq16

#check Compression.theorem33_eq17
#print axioms Compression.theorem33_eq17

#check Compression.corollary31_eq22
#print axioms Compression.corollary31_eq22

#check Compression.corollary31_eq24_lower
#print axioms Compression.corollary31_eq24_lower

#check Compression.theorem34_eq26
#print axioms Compression.theorem34_eq26

#check Compression.theorem34_eq27
#print axioms Compression.theorem34_eq27

#check Compression.theorem34_eq28
#print axioms Compression.theorem34_eq28

#check Compression.theorem35_paper
#print axioms Compression.theorem35_paper

#check Compression.theorem36_paper
#print axioms Compression.theorem36_paper

#check Compression.theorem37_shortestFeature
#print axioms Compression.theorem37_shortestFeature

#check Compression.theorem37_shortestBFeature
#print axioms Compression.theorem37_shortestBFeature

#check Compression.theorem38
#print axioms Compression.theorem38

#check Compression.theorem39
#print axioms Compression.theorem39

-- Section 4
#check Compression.theorem41
#print axioms Compression.theorem41

#check Compression.theorem41_current
#print axioms Compression.theorem41_current

-- Section 5
#check Compression.theorem51
#print axioms Compression.theorem51

#check Compression.theorem52_decoder
#print axioms Compression.theorem52_decoder

#check Compression.theorem52
#print axioms Compression.theorem52
