/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/ResidualQuotientOrbitIntegral.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

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
