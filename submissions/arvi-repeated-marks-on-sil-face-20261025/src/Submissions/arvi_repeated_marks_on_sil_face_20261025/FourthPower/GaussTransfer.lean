/- Copyright (c) 2026 Sil. Apache-2.0.
Fourth-power transfer for the actual Eisenstein Gauss sums, including nonunits.
The imported local Fourier and CRT theorems are from the OpenAI baseline. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.GaussUnits
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LocalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SixthFrequency
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.GaussEnergy

set_option autoImplicit false
namespace Candidate.FourthPower.GaussTransfer
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve CubicEisenstein ConcreteTraceCRT
open ProbePrimePower ProbePhysical CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

/-- Literal absence of fifth prime powers, not a coprimality condition on D. -/
def FifthFree (a : O) : Prop := ∀ p : O, Prime p → ¬p^5 ∣ a

theorem supported_divisor (a b : O) (ha : Supported (Ideal.span {a})) (hb : b ∣ a) :
    Supported (Ideal.span {b}) := by
  obtain ⟨c, hc⟩ := hb
  rw [hc, ← Ideal.span_singleton_mul_span_singleton, supported_mul_iff] at ha
  exact ha.1

theorem prime_power_nonunit_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n < 4)
    (D k : O) (hD : p ∣ D) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (D^4*k) = 0 := by
  obtain ⟨hg,hc⟩ := supported_prime_data p hp hs
  rw [sexticGauss_prime_power p hp hg]
  have hχ : actualSextic (Ideal.span {p}) hg^(n+1) ≠ 1 := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc (n+1)).mp he
    omega
  have hd : p^(n+1) ∣ D^4*k :=
    ((pow_dvd_pow p (by omega : n+1 ≤ 4)).trans (pow_dvd_pow_of_dvd hD 4)).mul_right k
  obtain ⟨q,hq⟩ := hd
  rw [hq, show p^(n+1)*q = p^n*(p*q) by ring]
  exact primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero _ hχ n (p*q)
    (dvd_mul_right p q)

theorem fifth_free_nonunit_zero (a : O) (ha : Supported (Ideal.span {a}))
    (hf : FifthFree a) (D k : O) (hcop : ¬IsCoprime D a) :
    sexticGauss a (supportedElement_ne_zero a ha) (D^4*k) = 0 := by
  have ha0 := supportedElement_ne_zero a ha
  have hex : ∃ p : O, Prime p ∧ p ∣ a ∧ p ∣ D := by
    by_contra! hn
    apply hcop
    exact (isCoprime_of_prime_dvd (by simp [ha0]) hn).symm
  obtain ⟨p,hp,hpa,hpD⟩ := hex
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp := supported_divisor a p ha hpa
  obtain ⟨b,hab,hpb⟩ := (FiniteMultiplicity.of_prime_left hp ha0).exists_eq_pow_mul_and_not_dvd
  have hbn : Supported (Ideal.span {b}) := by
    rw [hab, ← Ideal.span_singleton_mul_span_singleton, supported_mul_iff] at ha
    exact ha.2
  have hn : multiplicity p a < 5 := by
    by_contra! hh
    apply hf p hp
    exact (pow_dvd_pow p hh).trans ⟨b,hab⟩
  have hn0 : multiplicity p a ≠ 0 := by
    intro hz
    simp only [hz, pow_zero, one_mul] at hab
    exact hpb (hab ▸ hpa)
  have hpc : IsCoprime p b := hp.irreducible.coprime_iff_not_dvd.mpr hpb
  have hz := fun n (hn : n < 4) => prime_power_nonunit_zero p hp hsp n hn D k hpD
  generalize hv : multiplicity p a = v at hab hn hn0
  cases v with
  | zero => exact (hn0 rfl).elim
  | succ n =>
    subst a
    have hpow : Supported (Ideal.span {p^(n+1)}) :=
      supported_divisor _ _ ha (dvd_mul_right _ _)
    rw [sexticGauss_coprime_product _ b hpow hbn hpc.pow_left,
      hz n (by omega), mul_zero, zero_mul]

theorem fourth_power (a : O) (ha : Supported (Ideal.span {a}))
    (hf : FifthFree a) (D k : O) :
    sexticGauss a (supportedElement_ne_zero a ha) (D^4*k) =
      (idealRowHom D (Ideal.span {a}))^2 * sexticGauss a (supportedElement_ne_zero a ha) k := by
  by_cases hcop : IsCoprime D a
  · rw [sexticGauss_unit_scale a ha (D^4) k hcop.pow_left,
      idealRowHom_argument_pow D 4 _ ha]
    have h6 : (idealRowHom D (Ideal.span {a}))^6 = 1 := by
      rw [← idealRowHom_argument_pow D 6 _ ha, supported_sixth_value a D ha hcop.symm]
    rw [GaussUnits.inverse_fourth _ h6]
  · rw [fifth_free_nonunit_zero a ha hf D k hcop]
    have h6 : (idealRowHom D (Ideal.span {a}))^6 = 0 := by
      rw [← idealRowHom_argument_pow D 6 _ ha, idealRowHom_sixth_eq_mask D a ha]
      simp [coprimalityMask, hcop]
    have hz := eq_zero_of_pow_eq_zero h6
    rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul]

theorem normalized_fourth_power (a : O) (ha : Supported (Ideal.span {a}))
    (hf : FifthFree a) (D k : O) :
    gaussRow a ha (D^4*k) = (idealRowHom D (Ideal.span {a}))^2 * gaussRow a ha k := by
  unfold gaussRow
  rw [fourth_power a ha hf D k, mul_div_assoc]

/-- One common column vector over the entire D-family. No D-dependent
coefficient replacement or removal of natural zeros occurs here. -/
theorem whole_column {ι : Type*} (S : Finset ι) (a : ι → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (hf : ∀ i ∈ S, FifthFree (a i))
    (b : ι → ℂ) (D k : O) :
    (∑ i ∈ S, b i * (idealRowHom D (Ideal.span {a i}))^2 * gaussRow (a i) (ha i) k) =
      gaussPolynomial S a ha b (D^4*k) := by
  unfold gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalized_fourth_power (a i) (ha i) (hf i hi) D k, mul_assoc]

end
end Candidate.FourthPower.GaussTransfer
