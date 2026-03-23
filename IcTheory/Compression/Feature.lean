import IcTheory.Basics

namespace IcTheory

abbrev Program := BitString

/-- An abstract execution relation on binary-string programs.
`Runs p input output` means that program `p` can transform `input` into `output`. -/
abbrev Runs := Program → BitString → BitString → Prop

namespace Compression

/-- The paper's compression condition `|f| + |r| < |x|`. -/
def CompressionCondition (f r x : BitString) : Prop :=
  BitString.blen f + BitString.blen r < BitString.blen x

instance instDecidableCompressionCondition (f r x : BitString) :
    Decidable (CompressionCondition f r x) := by
  unfold CompressionCondition
  infer_instance

/-- `g` is a descriptive map for `x` given `f` if it produces a residual `r`
from which `f` reconstructs `x`, while satisfying the compression condition. -/
def IsDescriptiveMap (runs : Runs) (f g x : Program) : Prop :=
  ∃ r : BitString, runs g x r ∧ runs f r x ∧ CompressionCondition f r x

/-- The set of descriptive maps of `x` given `f`. -/
def descriptiveMaps (runs : Runs) (f x : Program) : Set Program :=
  {g | IsDescriptiveMap runs f g x}

/-- Residual descriptions reachable from `x` via some descriptive map for `f`. -/
def residualDescriptions (runs : Runs) (f x : Program) : Set BitString :=
  {r | ∃ g : Program, runs g x r ∧ runs f r x ∧ CompressionCondition f r x}

/-- `f` is a feature of `x` if some descriptive map exists for it. -/
def IsFeature (runs : Runs) (f x : Program) : Prop :=
  ∃ g : Program, IsDescriptiveMap runs f g x

/-- `f` is a shortest feature of `x` if it is a feature and no shorter feature exists. -/
def IsShortestFeature (runs : Runs) (f x : Program) : Prop :=
  IsFeature runs f x ∧ ∀ g : Program, IsFeature runs g x → BitString.blen f ≤ BitString.blen g

/-- `g` is a shortest descriptive map for `x` given `f` if it is descriptive and
no shorter descriptive-map program for `f` exists. -/
def IsShortestDescriptiveMap (runs : Runs) (f g x : Program) : Prop :=
  IsDescriptiveMap runs f g x ∧
    ∀ h : Program, IsDescriptiveMap runs f h x → BitString.blen g ≤ BitString.blen h

theorem isDescriptiveMap_iff (runs : Runs) (f g x : Program) :
    IsDescriptiveMap runs f g x ↔
      ∃ r : BitString, runs g x r ∧ runs f r x ∧ CompressionCondition f r x := by
  rfl

theorem mem_descriptiveMaps_iff (runs : Runs) (f x g : Program) :
    g ∈ descriptiveMaps runs f x ↔ IsDescriptiveMap runs f g x := by
  rfl

theorem mem_residualDescriptions_iff (runs : Runs) (f x r : BitString) :
    r ∈ residualDescriptions runs f x ↔
      ∃ g : Program, runs g x r ∧ runs f r x ∧ CompressionCondition f r x := by
  rfl

theorem shortestFeature_isFeature {runs : Runs} {f x : Program} :
    IsShortestFeature runs f x → IsFeature runs f x := by
  exact fun h => h.1

theorem shortestDescriptiveMap_isDescriptiveMap {runs : Runs} {f g x : Program} :
    IsShortestDescriptiveMap runs f g x → IsDescriptiveMap runs f g x := by
  exact fun h => h.1

end Compression

end IcTheory
