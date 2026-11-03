/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/ChamberSeries.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAnalyticity
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.EisensteinFourierContinuation
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem flat_entire (R : PrincipalMellin.ActualRecipe S η)
    (Q : AdmissibleFlatSources R) (v : R.A.UnitQuotient) (g : Group R) :
    Differentiable ℂ (fun s => (Q.flat v).val s g) :=
  KPLiteralExceptionalResidue.LiteralChamberAnalytic.flat_entire
    F R.A.zeta12 R.A.primitive_zeta12 Q.K Q.iwasawa (Q.flat v) g

end DedekindZetaZeroFree.EisensteinFourierContinuation

end
