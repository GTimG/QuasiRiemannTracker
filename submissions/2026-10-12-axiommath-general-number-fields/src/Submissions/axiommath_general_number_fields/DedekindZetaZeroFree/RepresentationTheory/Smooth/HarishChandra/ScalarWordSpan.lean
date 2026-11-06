/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/HarishChandra/ScalarWordSpan.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWordFiniteSums
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Periods.ResidualLieWordSpan
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordChamberReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources EisensteinSmoothGerms SharedSource
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming word_zero → word_zero
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
local notation "W" => KPContActualSphericalRightFieldIdentification.actualRightWord
  F R.A.zeta12 R.A.primitive_zeta12

def scalarWordSpan (T : Realization R Q) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ (Set.range (fun vw : R.A.UnitQuotient ×
    List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)) =>
      W vw.2 (T.theta vw.1)))

theorem realization_word_smooth (T : Realization R Q) (v : R.A.UnitQuotient)
    (a : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (W a (T.theta v)) :=
  actualRightWord_smooth _ (T.smooth v 0 (Metric.mem_ball_self T.radius_pos)) a

theorem scalarWordSpan_le_hcHeckeSpan (T : Realization R Q) :
    scalarWordSpan T ≤ hcHeckeSpan T := by
  apply Submodule.span_le.mpr
  rintro f ⟨⟨v, a⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨v, 1, a, ?_⟩
  have word_eq (w : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))) :
      W w (T.theta v) =
        AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12
          w (T.theta v) := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      simp only [KPContActualSphericalRightFieldIdentification.actualRightWord,
        AdelicRightLieWords.actualRightWord]
      rw [ih]
      rfl
  funext g
  simp [KPLiteralRaw.rightAction, word_eq]

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
