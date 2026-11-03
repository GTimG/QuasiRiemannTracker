/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/UpperPeriodDigitReindexing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Digits.SUnitReindexing

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.QuotientDescent
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem selected_upper_digit_reindex {N : TraceHaarTransport R} (C : JointMellinGaussianSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (u : R.A.U)
    (b : Bool) (y : R.A.G) (d : Digits R m) :
    (Integrable (fun q => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
        signedArgument R m b (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d))) C.sources.dq ∧
     Integrable (fun q => C.realization.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
        signedArgument R m b y d)) C.sources.dq) ∧
    upper R C.sources.dq (C.realization.theta v)
      (signedArgument R m b (R.A.diagonal (u.val ^ 6) * y) (digitReindex R m u d)) =
    upper R C.sources.dq (C.realization.theta v) (signedArgument R m b y d) := by
  refine ⟨⟨C.constantTerm.integrable v _, C.constantTerm.integrable v _⟩, ?_⟩
  exact (DedekindZetaZeroFree.DigitMasks.signed_term_reindex R C.realization v m u b y d).2
end DedekindZetaZeroFree.ThetaExpansion.QuotientDescent

end
