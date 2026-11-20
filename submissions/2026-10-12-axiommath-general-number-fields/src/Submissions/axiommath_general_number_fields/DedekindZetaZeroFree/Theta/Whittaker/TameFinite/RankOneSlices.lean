/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/TameFinite/RankOneSlices.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Whittaker.FinitePlaces.RootCovarianceAndTameRank

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.TensorActions
open MomentSources KPLocalExceptionalConstruction
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

theorem finite_slice_rank_le_one_tame (D : TensorActions R N) (q : KPFinitePlace F)
    (ht : (3 : (valuation (LocalField F q)).integer) ∉
      IsLocalRing.maximalIdeal (valuation (LocalField F q)).integer) :
    Module.rank ℂ (D.toTensorHC.sliceLine (Sum.inr q)) ≤ 1 :=
  D.finite_slice_rank_le_one_of_tame q ht

end DedekindZetaZeroFree.FourierContinuation.TensorActions

end
