/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/ConstantTerms/Scattering/TraceHaarContraction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.RationalFiberSlices
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.FiniteHaarTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLocalExceptionalConstruction KPRankOneShellRepair
open KPAdelicCoverRestrictedProduct MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

include P C in

theorem traceHaar_eq_smul_unit (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (q.adicCompletion F)).integer : Set _) = 1) :
    N.finiteHaar q = ENNReal.ofReal (PoissonS.integerVolume F q) • μ :=
  FourierContinuation.finiteHaar_transport N q ⟨C.canonical q, μ, hμ⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
