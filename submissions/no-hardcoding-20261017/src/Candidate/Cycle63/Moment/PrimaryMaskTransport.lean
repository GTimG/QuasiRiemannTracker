import Candidate.Cycle63.Moment.CanonicalPhaseCharacter
import Candidate.Cycle63.Density.NaturalMaskTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowPuncture

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ProbePhysical CenteredMomentFixedRay
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CanonicalRowCompletion
local notation "O" => HeckeFamily.O

/-- Primary-element identities determine every ideal coefficient after the
actual displayed Euler mask is restored. -/
theorem ideal_coefficient_mask_of_primary (χ ψ : Character)
    (hperiod : χ.modulus ≤ Ideal.span {(72:O)})
    (hprimary : ∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
      IsCoprime (Ideal.span {n}) χ.modulus → elementCoeff χ n = elementCoeff ψ n)
    (I : Ideal O) :
    idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  by_cases hI : I = 0
  · simp only [hI, idealCoeff_zero, ite_self]
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc]
    let n : O := idealGenerator I
    have hn : n ≠ 0 := idealGenerator_ne_zero I hI
    have hspan : Ideal.span {n} = I := span_idealGenerator I
    have hn72 : IsCoprime n (72:O) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [hspan]
      exact hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hperiod)
    have hsup : Supported I := by
      rw [← hspan]
      apply supported_of_coprime_bad (72:O) n _ _ hn72.symm
      · exact (dvd_pow_self goodLambda (by decide : (2:ℕ) ≠ 0)).trans
          (ActualEisensteinCubic.lambda_sq_dvd_three.trans ⟨24,by norm_num⟩)
      · exact ⟨36,by norm_num⟩
    have hp0 := supported_primaryGenerator_ne_zero I hsup
    have hp := primaryGenerator_spec I hp0
    have hs : Supported (Ideal.span {primaryGenerator I}) := by rw [hp.1]; exact hsup
    have hc' : IsCoprime (Ideal.span {primaryGenerator I}) χ.modulus := by
      rw [hp.1]; exact hc
    have he := hprimary (primaryGenerator I) hs hp.2 hc'
    rwa [← idealCoeff_span χ hp0, ← idealCoeff_span ψ hp0, hp.1] at he
  · have hh := idealCoeff_source_mask χ I
    simpa only [ite_eq_right hc] using hh

theorem natural_row_supported_element (η : Character) (z n : O)
    (F : NaturalRow η z) (hn : Supported (Ideal.span {n})) :
    elementCoeff F.character n = elementCoeff η n * idealRowHom z (Ideal.span {n}) := by
  rw [F.element, rowTwist_extract_sixth_mask _ fixedBadMask 1 z n hn]
  change elementCoeff η n * coprimalityMask fixedBadMask n *
    idealRowHom (1^4*z) (Ideal.span {n}) = _
  rw [show coprimalityMask fixedBadMask n = (1:ℂ) by
    exact ite_eq_left (fixedBadMask_coprime n hn)]
  simp only [one_pow, one_mul, mul_one]

theorem natural_row_mask_of_primary (η χ : Character) (z : O)
    (F : NaturalRow η z) (hperiod : χ.modulus ≤ Ideal.span {(72:O)})
    (hprimary : ∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
      IsCoprime (Ideal.span {n}) χ.modulus →
      elementCoeff χ n = elementCoeff η n * idealRowHom z (Ideal.span {n}))
    (I : Ideal O) :
    idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  apply ideal_coefficient_mask_of_primary χ F.character hperiod
  intro n hn hp hc
  rw [hprimary n hn hp hc, natural_row_supported_element η z n F hn]

theorem natural_parent_supported_element (η : Character) (z n : O)
    (F : NaturalRow η z) (R : Ideal O) (hn : Supported (Ideal.span {n}))
    (hc : IsCoprime (Ideal.span {n}) (excluded F.character R).modulus) :
    elementCoeff (excluded F.character R) n =
      elementCoeff η n * idealRowHom z (Ideal.span {n}) := by
  have hn0 : n ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hn.1
  rw [← idealCoeff_span _ hn0]
  change idealCoeff (F.character.excludePrimes (primeSupport R) (support_prime R))
    (Ideal.span {n}) = _
  change IsCoprime (Ideal.span {n})
    (F.character.excludePrimes (primeSupport R) (support_prime R)).modulus at hc
  rw [excludePrimes_mask, ite_eq_left hc, idealCoeff_span F.character hn0]
  exact natural_row_supported_element η z n F hn

theorem natural_row_supported_ideal (η : Character) (z : O) (F : NaturalRow η z)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff F.character I = idealCoeff η I * idealRowHom z I := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primaryGenerator_spec I hn
  rw [← hs.1, idealCoeff_span F.character hn, idealCoeff_span η hn]
  exact natural_row_supported_element η z _ F (by rw [hs.1]; exact hI)

theorem natural_row_ideal_zero_of_not_supported (η : Character) (z : O)
    (F : NaturalRow η z) (I : Ideal O) (hI : ¬Supported I) :
    idealCoeff F.character I = 0 := by
  by_cases hz : I = 0
  · rw [hz, idealCoeff_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I hz
  have hs : Ideal.span {n} = I := span_idealGenerator I
  rw [← hs, idealCoeff_span F.character hn, F.element]
  exact rowTwist_zero_of_not_supported _ _ _ _ _
    (dvd_mul_right _ _) (dvd_mul_left _ _) (by rwa [hs])

#print axioms ideal_coefficient_mask_of_primary
#print axioms natural_row_supported_element
#print axioms natural_row_mask_of_primary
#print axioms natural_parent_supported_element
#print axioms natural_row_supported_ideal
#print axioms natural_row_ideal_zero_of_not_supported
end
end OAI.SevenEighths.Cycle63Moment
