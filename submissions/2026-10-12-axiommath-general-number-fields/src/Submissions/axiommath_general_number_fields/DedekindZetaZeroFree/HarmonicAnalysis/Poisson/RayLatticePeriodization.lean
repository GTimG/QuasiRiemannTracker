/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Poisson/RayLatticePeriodization.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Γ : Submodule ℤ E) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

variable (ν : Measure E) [ν.IsAddHaarMeasure]
    (D : Set E) (hD : MeasurableSet D)
    (hfund : IsAddFundamentalDomain Γ D ν)

include hD hfund

instance latticeVAddInvariant : VAddInvariantMeasure Γ E ν :=
  ⟨fun γ s _ => measure_preimage_add ν (γ : E) s⟩

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
