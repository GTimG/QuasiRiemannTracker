import ZetaZeroFree.Analytic.Moments.Sharp
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

namespace ZetaZeroFree.Analytic.Moments.D3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentRadicalFamily
open CenteredMomentSourceRow

local notation "O" => HeckeFamily.O

/-- Naturalizing a character with the fixed bad-prime zeros does not alter its row coefficients. -/
theorem naturalPlainCharacter_ideal_of_fixed_zeros
    (η : Character) (hη : ∀ I : Ideal O, ¬ Supported I → idealCoeff η I = 0)
    (k : O) (hk : k ≠ 0) (I : Ideal O) :
    idealCoeff (naturalPlainCharacter η k) I = idealCoeff η I * idealRowHom k I := by
  rw [naturalPlainCharacter, dite_eq_left hk, NaturalRow.ideal]
  by_cases hI : Supported I
  · rw [idealRowHom_argument_mul, idealRowHom_sixth_mask fixedBadMask I hI,
      ite_eq_left ?_, one_mul]
    have hcop : IsCoprime (Ideal.span {fixedBadMask}) I := by
      rw [← primary_span_supported I hI, Ideal.isCoprime_span_singleton_iff]
      exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
    exact hcop.symm
  · rw [hη I hI, zero_mul, zero_mul]

theorem excluded_naturalPlainCharacter_ideal
    (η : Character) (hη : ∀ I : Ideal O, ¬ Supported I → idealCoeff η I = 0)
    (k : O) (hk : k ≠ 0) (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff (excluded (naturalPlainCharacter η k) R) I =
      if IsCoprime I R then idealCoeff η I * idealRowHom k I else 0 := by
  rw [excluded_ideal _ R hR, naturalPlainCharacter_ideal_of_fixed_zeros η hη k hk I]

/-- Adding a common puncture preserves the primitive principal/nonprincipal distinction. -/
theorem excluded_nonprincipal_iff (χ : Character) (R : Ideal O) :
    (excluded χ R).residue ≠ 1 ↔ χ.residue ≠ 1 := by
  exact not_congr (HeckeFiniteDeletion.principal_iff_of_mask _ _
    (excludePrimes_mask χ (CompletedGauss.primeSupport R) (support_prime R)))

/-- A product of displayed moving prime powers has radical conductor cost.
Positive representatives include six and retain the displayed zeros. -/
theorem exists_moving_radical_presentation {ι : Type*} [Fintype ι]
    (ν : Character) (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (e : ι → ℕ) (he : ∀ i, 0 < e i) :
    ∃ η : Character,
      η.modulus.absNorm ≤ ν.modulus.absNorm * fixedConductorFactor *
        ∏ i, (Ideal.span {p i}).absNorm ∧
      (∀ n : O, elementCoeff η n =
        rowTwist (elementHom ν) fixedBadMask 1 (∏ i, p i ^ e i) n) ∧
      (∀ I : Ideal O, ¬ Supported I → idealCoeff η I = 0) := by
  obtain ⟨η, _, hnorm, helement⟩ := exists_radical_row_presentation ν
    fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) p hp e he
  refine ⟨η, by simpa only [fixedConductorFactor, mul_assoc] using hnorm, helement, ?_⟩
  intro I hI
  by_cases hI0 : I = 0
  · subst I
    exact idealCoeff_zero η
  · rw [← span_idealGenerator I, idealCoeff_span η (idealGenerator_ne_zero I hI0),
      helement]
    exact rowTwist_zero_of_not_supported _ _ _ _ _
      (dvd_mul_right _ _) (dvd_mul_left _ _) (by simpa only [span_idealGenerator] using hI)


/-- The radical presentation has the literal product of residue symbols at every ideal.
The fixed bad-prime zeros are already part of the fixed base character. -/
theorem radical_presentation_ideal {ι : Type*} [Fintype ι]
    (ν η : Character) (p : ι → O) (e : ι → ℕ)
    (hν : ∀ I : Ideal O, ¬ Supported I → idealCoeff ν I = 0)
    (hη : ∀ I : Ideal O, ¬ Supported I → idealCoeff η I = 0)
    (helement : ∀ n : O, elementCoeff η n =
      rowTwist (elementHom ν) fixedBadMask 1 (∏ i, p i ^ e i) n)
    (I : Ideal O) :
    idealCoeff η I = idealCoeff ν I * ∏ i, (idealRowHom (p i) I) ^ e i := by
  by_cases hI : Supported I
  · have hbase : idealCoeff η I =
        idealCoeff ν I * idealRowHom (fixedBadMask ^ 6 * (∏ i, p i ^ e i)) I := by
      simpa only [one_pow, mul_one] using
        idealCoeff_eq_row ν η fixedBadMask 1 (∏ i, p i ^ e i) helement I
    have hcop : IsCoprime (Ideal.span {fixedBadMask}) I := by
      rw [← primary_span_supported I hI, Ideal.isCoprime_span_singleton_iff]
      exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
    have hprod (s : Finset ι) :
        idealRowHom (∏ i ∈ s, p i ^ e i) I =
          ∏ i ∈ s, (idealRowHom (p i) I) ^ e i := by
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using idealRowHom_one_supported I hI
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi,
          idealRowHom_argument_mul, idealRowHom_argument_pow _ _ _ hI, ih]
    rw [hbase, idealRowHom_argument_mul, idealRowHom_sixth_mask fixedBadMask I hI,
      if_pos hcop.symm, one_mul, hprod Finset.univ]
  · rw [hη I hI, hν I hI, zero_mul]

end
end ZetaZeroFree.Analytic.Moments.D3
