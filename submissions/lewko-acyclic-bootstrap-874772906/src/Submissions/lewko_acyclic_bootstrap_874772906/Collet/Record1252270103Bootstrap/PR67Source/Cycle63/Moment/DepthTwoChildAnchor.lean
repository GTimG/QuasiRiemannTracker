import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoDictionary
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- A second-stage character is a natural row of itself at the row `1`, and excluding the unit ideal from it keeps its
modulus and its coefficients; so a first-level child can serve as the anchor of the first-level dictionary lemmas.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondExceptionalFamily CenteredMomentCanonicalFirst CenteredMomentChildRows
local notation "O" => HeckeFamily.O

/-- A second-stage character has nonzero coefficients only at elements with supported ideals: its coefficients are the
row twist of a child character, whose modulus lies below `(12)`. -/
theorem family_element_supported (η : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (ξ : RayCharacter) (n : O) (hn : elementCoeff (τ ξ) n ≠ 0) : Supported (Ideal.span {n}) := by
  have hchild : elementCoeff (childCharacter η ξ) n ≠ 0 := by
    intro h0
    apply hn
    rw [hf.element_eq ξ n]
    change elementCoeff (childCharacter η ξ) n*_ = 0
    rw [h0, zero_mul]
  have hcop := old_coefficient_nonzero_coprime _ n hchild
  rw [childCharacter_modulus] at hcop
  have h12 : IsCoprime (Ideal.span {n}) (Ideal.span {(12 : O)}) :=
    hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr inf_le_right)
  have h3 : goodLambda ∣ (3 : O) := CubicEisenstein.halfPrimary_lambda_dvd_three
  exact ProbePhysical.supported_of_coprime_bad 12 n (h3.trans ⟨4, by norm_num⟩) ⟨6, by norm_num⟩
    ((Ideal.isCoprime_span_singleton_iff _ _).mp h12).symm

/-- A second-stage character vanishes at zero. -/
theorem family_element_zero (η : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (ξ : RayCharacter) : elementCoeff (τ ξ) 0 = 0 := by
  by_contra h
  have hs := family_element_supported η C D hC hD U τ hf ξ 0 h
  exact hs.1 (by rw [Ideal.span_singleton_zero, Ideal.zero_eq_bot])

/-- A character whose nonzero coefficients sit at elements with supported ideals is a natural row of itself at the
row `1`. -/
def selfNaturalRow (σ : Character) (hσ : ∀ n : O, elementCoeff σ n ≠ 0 → Supported (Ideal.span {n})) :
    NaturalRow σ 1 where
  character := σ
  modulus_bound := by
    have hm : 1 ≤ (Ideal.span {fixedBadMask} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    have h72 : 1 ≤ (Ideal.span {(72 : O)} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    simp only [rowConductorBound, Ideal.span_singleton_one, Ideal.absNorm_top, one_pow, mul_one]
    exact (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt hm)).trans
      (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt h72))
  element := fun n => by
    by_cases hs : Supported (Ideal.span {n})
    · have hcop : IsCoprime (Ideal.span {n}) (Ideal.span {fixedBadMask}) :=
        (Ideal.isCoprime_span_singleton_iff _ _).mpr (fixedBadMask_coprime n hs).symm
      have hrow := idealRowHom_sixth_mask fixedBadMask (Ideal.span {n}) hs
      rw [ite_eq_left hcop] at hrow
      change elementCoeff _ n = elementCoeff _ n*idealRowHom (fixedBadMask^6*1^4*1) _
      simp only [one_pow, mul_one]
      change elementCoeff _ n = elementCoeff _ n*idealRowHom (fixedBadMask^6) (Ideal.span {n})
      rw [hrow, mul_one]
    · have hz : elementCoeff σ n = 0 := by
        by_contra h
        exact hs (hσ n h)
      change elementCoeff _ n = elementCoeff _ n*idealRowHom _ _
      rw [hz, zero_mul]

/-- The natural row of a character at the row `1` built by `selfNaturalRow` has the character itself. -/
theorem selfNaturalRow_character (σ : Character) (hσ : ∀ n : O, elementCoeff σ n ≠ 0 → Supported (Ideal.span {n})) :
    (selfNaturalRow σ hσ).character = σ := rfl

/-- Excluding the unit ideal from a character keeps its modulus. -/
theorem excluded_one_modulus (σ : Character) : (excluded σ 1).modulus = σ.modulus := by
  have hsupport : CompletedGauss.primeSupport (1 : Ideal O) = ∅ := by
    change UniqueFactorizationMonoid.primeFactors (1 : Ideal O) = ∅
    exact UniqueFactorizationMonoid.primeFactors_one
  change σ.modulus*∏ P ∈ CompletedGauss.primeSupport (1 : Ideal O), P = σ.modulus
  rw [hsupport, Finset.prod_empty, mul_one]

/-- Excluding the unit ideal from a character that vanishes at zero keeps its coefficients. -/
theorem excluded_one_element (σ : Character) (hσ0 : elementCoeff σ 0 = 0) (n : O) :
    elementCoeff (excluded σ 1) n = elementCoeff σ n := by
  rw [excluded_element σ hσ0 1 one_ne_zero n, ite_eq_left isCoprime_one_right]

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
