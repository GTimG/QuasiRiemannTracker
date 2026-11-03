/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/FrequencyNormValuations.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.MaskedPrimitiveInducers

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem actual_frequency_norm_dictionary
    (R : PrincipalMellin.ActualRecipe S η) (u : Frequency R) :
    frequencyNorm R u = (Detector.frequencyNorm F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) u.val.val : ℝ) ∧
    1 ≤ frequencyNorm R u := by
  refine ⟨rfl, ?_⟩
  change (1 : ℝ) ≤ (Detector.frequencyNorm F _ u.val.val : ℝ)
  exact_mod_cast (Detector.exterior_frequency_support_finite_norm_pos F _
    R.A.Sf.finite_toSet u.val.val u.val.property).2.2

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
