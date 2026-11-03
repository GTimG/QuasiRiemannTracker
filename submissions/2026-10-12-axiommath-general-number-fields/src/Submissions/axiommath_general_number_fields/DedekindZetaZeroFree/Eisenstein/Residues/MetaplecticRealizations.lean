/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/MetaplecticRealizations.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree
namespace KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def period (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (μ : Measure (KPAdditiveQuotient F)) (f : Functions F ζ hζ) : ℂ :=
  ∫ x, f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x)) * star (ψ.toAddChar x) ∂μ

end KPLiteralRaw

end DedekindZetaZeroFree

end
