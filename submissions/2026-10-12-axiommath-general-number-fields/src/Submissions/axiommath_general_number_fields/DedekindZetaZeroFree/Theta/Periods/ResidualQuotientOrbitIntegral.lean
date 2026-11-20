/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/ResidualQuotientOrbitIntegral.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw
open KPGlobalResidualConstruction MeasureTheory NumberField
open scoped Topology
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

def characterCircle (ψ : ContinuousAddChar (KPAdditiveQuotient F)) : C(Y F, Circle) :=
  ⟨fun x => ⟨ψ.toFun x, by simpa [Submonoid.unitSphere] using ψ.unitary x⟩,
    ψ.continuous_toFun.subtype_mk (fun x => by simpa [Submonoid.unitSphere] using ψ.unitary x)⟩

end DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw

end
