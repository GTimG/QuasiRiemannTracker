/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Compact/CompactCharacterProjectors.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

namespace DedekindZetaZeroFree.CompactProjectors

open MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {K H E F : Type*}

def IsStable [Monoid K] [AddCommGroup H] [Module ℂ H]
    (ρ : Representation ℂ K H) (C : Submodule ℂ H) : Prop :=
  ∀ (k : K) (x : H), x ∈ C → ρ k x ∈ C

end DedekindZetaZeroFree.CompactProjectors
