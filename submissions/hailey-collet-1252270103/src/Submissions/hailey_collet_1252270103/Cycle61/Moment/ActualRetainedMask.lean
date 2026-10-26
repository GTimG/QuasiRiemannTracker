import Submissions.hailey_collet_1252270103.Cycle61.Moment.SecondNaturalMask
import Submissions.hailey_collet_1252270103.Cycle61.Moment.WholeSourceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows IdealMobiusDivisorSum
open CenteredMomentHeckeColumnWindow CenteredMomentSecondChildProfile
local notation "O" => HeckeFamily.O

theorem actual_reduced_family_supported_ideal (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (χ : RayCharacter) (I : Ideal O) (hI : Supported I) :
    idealCoeff (τ χ) I = idealCoeff (childCharacter η χ) I *
      idealRowHom (reducedNumerator C D U) I := by
  have h := CenteredMomentSecondFamilyTransport.row_presentation_height
    η (τ χ) χ (reducedNumerator C D U) (hf.element_eq χ) I hI 0
  simp only [heightCoeff, Complex.ofReal_zero, mul_zero, Complex.cpow_zero,
    mul_one] at h
  rw [child_ideal_primary η χ I hI, h]
  ring

/-- The physical puncture restores the sixth factors cancelled in the second
character presentation; no conductor comparison for that presentation is used. -/
theorem actual_retained_reduced_mask (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (χ : RayCharacter) (z : O) (F : NaturalRow (τ χ) z)
    (G : NaturalRow (childCharacter η χ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (P : Ideal O) (hP : P ≠ 0) (hCP : C ∣ P) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded G.character P) I := by
  rw [excluded_ideal _ _ hP, excluded_ideal _ _ hP]
  by_cases hc : IsCoprime I P
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hs : Supported I
    · rw [natural_row_supported_ideal _ _ F I hs,
        natural_row_supported_ideal _ _ G I hs,
        actual_reduced_family_supported_ideal η C D hC hD U τ hf χ I hs,
        idealRowHom_argument_mul,
        residual_sixth_coefficient C D hC hCD U I hs
          (hc.of_isCoprime_of_dvd_right hCP).symm]
      ring
    · rw [natural_row_ideal_zero_of_not_supported _ _ F I hs,
        natural_row_ideal_zero_of_not_supported _ _ G I hs]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem actual_retained_fixed_dictionary_mask (η χ₁ : Character) (w : O)
    (first : NaturalRow η w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (ξ : RayCharacter) (z : O) (F : NaturalRow (τ ξ) z)
    (second : NaturalRow (childCharacter χ₁ ξ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (fixed : NaturalRow (childCharacter η ξ)
      (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (P : Ideal O) (hP : P ≠ 0) (hCP : C ∣ P) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded fixed.character (χ₁.modulus * P)) I := by
  rw [actual_retained_reduced_mask χ₁ C D hC hD hCD U τ hf ξ z F second P hP hCP I]
  exact actual_second_punctured_natural_mask η χ₁ w _ first hfirst ξ second fixed P hP I

#print axioms actual_reduced_family_supported_ideal
#print axioms actual_retained_reduced_mask
#print axioms actual_retained_fixed_dictionary_mask

section WholeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_retained_whole_dictionary_mask (η₀ η χ₁ : Character) (w : O)
    (first : NaturalRow η w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (ξ : RayCharacter) (z : O) (F : NaturalRow (τ ξ) z)
    (second : NaturalRow (childCharacter χ₁ ξ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (fixed : NaturalRow (childCharacter η ξ)
      (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (P : Ideal O) (hP : P ≠ 0) (hCP : C ∣ P)
    (hw : w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z) ≠ 0)
    (G : ∀ j : WholeSourceIndex M H,
      NaturalRow (wholeSourceBase M H hH η₀ (childCharacter η ξ) j)
        (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ (excluded F.character P) j) I =
      idealCoeff (excluded (G j).character (χ₁.modulus * P)) I := by
  exact whole_source_family_mask M H hH η₀ (childCharacter η ξ)
    (excluded F.character P) _ hw fixed _ (mul_ne_zero χ₁.modulus_ne_bot hP)
    (actual_retained_fixed_dictionary_mask η χ₁ w first hfirst
      C D hC hD hCD U τ hf ξ z F second fixed P hP hCP) G j I

#print axioms actual_retained_whole_dictionary_mask
end WholeFamily
end
end OAI.SevenEighths.Cycle61Moment
