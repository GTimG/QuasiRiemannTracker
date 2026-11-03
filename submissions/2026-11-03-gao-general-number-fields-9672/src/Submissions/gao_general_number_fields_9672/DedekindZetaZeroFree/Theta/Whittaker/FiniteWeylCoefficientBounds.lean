/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/FiniteWeylCoefficientBounds.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.FiniteWeylUniformBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem finite_weyl_value_bounds (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointDigitDescentSources R N) :
    ∃ M D : ℝ, 0 < M ∧ 0 ≤ D ∧ ∀ v (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ),
      ‖normalizedLocalWeylValue R C v (Sum.inr p.val) z‖ ≤
        D * finitePowerMajorant M ‖(z : p.val.adicCompletion F)‖ := by
  exact SheetRescaling.finite_weyl_bounds R C
end DedekindZetaZeroFree.ThetaExpansion

end
