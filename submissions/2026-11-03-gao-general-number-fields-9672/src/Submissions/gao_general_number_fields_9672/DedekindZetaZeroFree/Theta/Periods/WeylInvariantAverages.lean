/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/WeylInvariantAverages.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Digits.FiniteCharacterMasks
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField MeasureTheory
open scoped Classical BigOperators
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem rationalLift_mk (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12
      (Matrix.ProjGenLinGroup.mk g) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.rationalHom F R.A.zeta12 R.A.primitive_zeta12 g) := by
  rw [KPLiteralExceptionalResidue.rationalLift_eq_constructed]
  exact (KPGlobalResidualConstruction.ElementaryOutputs.rationalSplitting
    F R.A.zeta12 R.A.primitive_zeta12).on_matrix g

end DedekindZetaZeroFree.DigitMasks

end
