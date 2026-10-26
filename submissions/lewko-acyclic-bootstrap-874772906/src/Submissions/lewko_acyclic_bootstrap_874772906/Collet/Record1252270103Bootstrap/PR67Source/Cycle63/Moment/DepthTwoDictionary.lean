import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ActualRetainedMask
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ActualRowDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The four-ray dictionary of the depth-two rows, and the identities that present the character of a first-level
child and the natural rows over it in that dictionary, off the child's holes. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows CenteredMomentFixedRay IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- The fixed dictionary of the depth-two rows: the two-ray dictionary of the first level, applied twice. -/
def fourFixedDictionary (η₀ : Character) (j : (RayCharacter × RayCharacter) × (RayCharacter × RayCharacter)) :
    Character :=
  secondFixedDictionary (secondFixedDictionary η₀ j.1) j.2

/-- An ideal coprime to the fixed bad mask is supported. -/
theorem supported_of_coprime_fixedBadMask (I : Ideal O) (hI : IsCoprime I (Ideal.span {fixedBadMask})) :
    Supported I := by
  rw [← span_idealGenerator I] at hI ⊢
  have hc : IsCoprime (idealGenerator I) fixedBadMask := (Ideal.isCoprime_span_singleton_iff _ _).mp hI
  have hlam : IsCoprime goodLambda (idealGenerator I) := hc.symm.of_isCoprime_of_dvd_left (dvd_mul_right _ _)
  have htwo : IsCoprime (2 : O) (idealGenerator I) := hc.symm.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
  apply (supported_span_iff _).mpr
  refine ⟨PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp hlam, ?_⟩
  have hneg : IsCoprime (-2 : O) (idealGenerator I) := htwo.of_isCoprime_of_dvd_left ⟨-1, by ring⟩
  simpa only [neg_dvd] using negative_two_prime.irreducible.coprime_iff_not_dvd.mp hneg

/-- The second-stage character of a first-level child, excluded by a puncture `P` times the fixed bad mask, where every
ideal coprime to `P` is coprime to its first common ideal, is the two-ray dictionary member at the child multiplier
`w (G V)`, excluded by the column modulus times that puncture: the row identity of the first level at the row `1`. -/
theorem child_character_dictionary_mask (η χ₁ : Character) (w : O) (first : NaturalRow η w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (ξ : RayCharacter) (hv : w*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) ≠ 0)
    (P : Ideal O) (hP : P ≠ 0) (hcop : ∀ J : Ideal O, IsCoprime J P → IsCoprime J C) (I : Ideal O) :
    idealCoeff (excluded (τ ξ) (P*Ideal.span {fixedBadMask})) I =
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (w*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) hv).character
          (χ₁.modulus*(P*Ideal.span {fixedBadMask}))) I := by
  have hb : Ideal.span {fixedBadMask} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact fixedBadMask_ne_zero
  have hP' : P*Ideal.span {fixedBadMask} ≠ 0 := mul_ne_zero hP hb
  have hGV : (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*1 ≠ 0 := by
    rw [mul_one]
    exact (mul_ne_zero_iff.mp hv).2
  have hwGV : w*((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*1) ≠ 0 := by
    rw [mul_one]
    exact hv
  have h := actual_retained_fixed_dictionary_mask η χ₁ w first hfirst C D hC hD hCD U τ hf ξ 1
    (naturalRow (τ ξ) 1 one_ne_zero) (naturalRow (childCharacter χ₁ ξ) _ hGV)
    (naturalRow (childCharacter η ξ) _ hwGV) (P*Ideal.span {fixedBadMask}) hP'
    (fun J h => hcop J (h.of_isCoprime_of_dvd_right (dvd_mul_right P _))) I
  have e₂ : idealCoeff (naturalRow (childCharacter η ξ) _ hwGV).character I =
      idealCoeff (naturalRow (childCharacter η ξ) _ hv).character I := by
    rw [NaturalRow.ideal, NaturalRow.ideal, mul_one]
  rw [excluded_ideal _ _ hP', excluded_ideal _ _ (mul_ne_zero χ₁.modulus_ne_bot hP'), e₂] at h
  rw [excluded_ideal _ _ hP', excluded_ideal _ _ (mul_ne_zero χ₁.modulus_ne_bot hP')]
  by_cases hc : IsCoprime I (P*Ideal.span {fixedBadMask})
  · have hs : Supported I := supported_of_coprime_fixedBadMask I (hc.of_isCoprime_of_dvd_right (dvd_mul_left _ _))
    have e₁ : idealCoeff (naturalRow (τ ξ) 1 one_ne_zero).character I = idealCoeff (τ ξ) I := by
      rw [natural_row_supported_ideal _ _ _ I hs, idealRowHom_one_supported I hs, mul_one]
    rw [ite_eq_left hc, e₁] at h
    rw [ite_eq_left hc]
    exact h
  · rw [ite_eq_right hc] at h
    rw [ite_eq_right hc]
    exact h

/-- Natural rows over a character that is, off a puncture `P`, a natural row of `η` at `u` excluded by `H` are, off a
puncture `Q ⊇ P`, the natural rows of the same two-ray child of `η` at the product row, excluded by `H Q`. -/
theorem masked_natural_row_compose (η σ : Character) (u : O) (F₁ : NaturalRow η u) (P H : Ideal O)
    (hP : P ≠ 0) (hH : H ≠ 0)
    (hσ : ∀ I : Ideal O, idealCoeff (excluded σ P) I = idealCoeff (excluded F₁.character H) I)
    (j : RayCharacter × RayCharacter) (z : O) (G : NaturalRow (secondFixedDictionary σ j) z)
    (G' : NaturalRow (secondFixedDictionary η j) (u*z)) (Q : Ideal O) (hQ : Q ≠ 0) (hPQ : P ∣ Q)
    (I : Ideal O) :
    idealCoeff (excluded G.character Q) I = idealCoeff (excluded G'.character (H*Q)) I := by
  rw [excluded_ideal _ _ hQ, excluded_ideal _ _ (mul_ne_zero hH hQ), IsCoprime.mul_right_iff]
  by_cases hq : IsCoprime I Q
  swap
  · rw [ite_eq_right hq, ite_eq_right (fun h' => hq h'.2)]
  rw [ite_eq_left hq]
  by_cases hs : Supported I
  swap
  · rw [natural_row_ideal_zero_of_not_supported _ _ G I hs, natural_row_ideal_zero_of_not_supported _ _ G' I hs,
      ite_self]
  have h := hσ I
  rw [excluded_ideal _ _ hP, excluded_ideal _ _ hH, ite_eq_left (hq.of_isCoprime_of_dvd_right hPQ)] at h
  have hG : idealCoeff G.character I = idealCoeff σ I*(idealCoeff (primaryRayCharacter j.1) I*
      idealCoeff (primaryRayCharacter j.2) I)*idealRowHom z I := by
    rw [natural_row_supported_ideal _ _ G I hs]
    simp only [secondFixedDictionary, childCharacter, idealCoeff_product]
    ring
  have hG' : idealCoeff G'.character I = idealCoeff η I*idealRowHom u I*(idealCoeff (primaryRayCharacter j.1) I*
      idealCoeff (primaryRayCharacter j.2) I)*idealRowHom z I := by
    rw [natural_row_supported_ideal _ _ G' I hs, idealRowHom_argument_mul]
    simp only [secondFixedDictionary, childCharacter, idealCoeff_product]
    ring
  rw [hG, hG', h]
  by_cases hh : IsCoprime I H
  · rw [ite_eq_left hh, ite_eq_left ⟨hh, hq⟩, natural_row_supported_ideal _ _ F₁ I hs]
  · rw [ite_eq_right hh, ite_eq_right (fun h' => hh h'.1), zero_mul, zero_mul]

/-- The natural rows over the second-stage character of a first-level child at a row `z`, off a puncture containing
the child's puncture and the fixed bad mask, are the natural rows of the four-ray dictionary member at the child
multiplier times `z`, excluded by the child's holes times that puncture. -/
theorem child_natural_row_four_dictionary (η₀ : Character) (j₁ j₂ : RayCharacter × RayCharacter)
    (χ₁ : Character) (w : O) (first : NaturalRow (childCharacter η₀ j₁.1) w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I χ₁.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (hv : w*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) ≠ 0)
    (P : Ideal O) (hP : P ≠ 0) (hcop : ∀ J : Ideal O, IsCoprime J P → IsCoprime J C) (z : O)
    (G : NaturalRow (secondFixedDictionary (τ j₁.2) j₂) z)
    (G' : NaturalRow (fourFixedDictionary η₀ (j₁, j₂))
      ((w*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))*z))
    (Q : Ideal O) (hQ : Q ≠ 0) (hPQ : P*Ideal.span {fixedBadMask} ∣ Q) (I : Ideal O) :
    idealCoeff (excluded G.character Q) I =
      idealCoeff (excluded G'.character ((χ₁.modulus*(P*Ideal.span {fixedBadMask}))*Q)) I := by
  have hb : Ideal.span {fixedBadMask} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact fixedBadMask_ne_zero
  have hP' : P*Ideal.span {fixedBadMask} ≠ 0 := mul_ne_zero hP hb
  exact masked_natural_row_compose (secondFixedDictionary η₀ j₁) (τ j₁.2)
    (w*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
    (naturalRow (childCharacter (childCharacter η₀ j₁.1) j₁.2) _ hv) (P*Ideal.span {fixedBadMask})
    (χ₁.modulus*(P*Ideal.span {fixedBadMask})) hP' (mul_ne_zero χ₁.modulus_ne_bot hP')
    (child_character_dictionary_mask (childCharacter η₀ j₁.1) χ₁ w first hfirst C D hC hD hCD U τ hf j₁.2 hv
      P hP hcop)
    j₂ z G G' Q hQ hPQ I

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
