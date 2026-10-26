/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact squarefree-at-the-pool sixth-frequency mask, including nonunit frequencies.
Uses the original OpenAI/math sextic Gauss sum and its CRT normalization. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationGlobal

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentAmplification CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

/-- A primitive sextic local factor vanishes at every prime-divisible frequency. -/
theorem sexticGauss_prime_dvd_zero (p : O) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (H : O) (hH : p ∣ H) :
    sexticGauss p hp.ne_zero H = 0 := by
  have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
    intro he
    have ho := CenteredMomentCanonical.actualSextic_order_six (Ideal.span {p}) hg hc
    rw [he,orderOf_one] at ho
    norm_num at ho
  have hz := primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero
    (actualSextic (Ideal.span {p}) hg) hχ 0 H hH
  have he := sexticGauss_prime_power p hp hg 0 H
  simp only [zero_add,pow_one,pow_zero,one_mul] at he hz
  exact he.trans hz

/-- CA3 for the literal Gauss sum. Only squarefreeness at p is needed.
There is no condition on h, so natural zeros and the zero frequency remain exact. -/
theorem sexticGauss_pool_prime_mask (a p : O)
    (ha : Supported (Ideal.span {a})) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hsq : ¬p^2 ∣ a) (h : O) :
    sexticGauss a (supportedElement_ne_zero a ha) (p^6*h) =
      if p ∣ a then 0 else sexticGauss a (supportedElement_ne_zero a ha) h := by
  by_cases hd : p ∣ a
  · rw [ite_eq_left hd]
    obtain ⟨r,hr⟩ := hd
    have hpr : ¬p ∣ r := by
      rintro ⟨s,hs⟩
      apply hsq
      refine ⟨s,?_⟩
      rw [hr,hs]
      ring
    have hcop : IsCoprime p r := hp.irreducible.coprime_iff_not_dvd.mpr hpr
    have hrSupport : Supported (Ideal.span {r}) := by
      have hfull := ha
      rw [hr,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] at hfull
      exact hfull.2
    have hz := sexticGauss_prime_dvd_zero p hp hg hc (p^6*h)
      (dvd_mul_of_dvd_left (dvd_pow_self p (by decide : 6 ≠ 0)) h)
    have hproduct := sexticGauss_coprime_product p r hs hrSupport hcop (p^6*h)
    simp only [hz,mul_zero,zero_mul] at hproduct
    simpa only [hr] using hproduct
  · rw [ite_eq_right hd]
    exact gauss_sixth_frequency a ha p h
      (hp.irreducible.coprime_iff_not_dvd.mpr hd)

/-- The same mask holds with the exact original central Gauss normalization. -/
theorem gaussRow_pool_prime_mask (a p : O)
    (ha : Supported (Ideal.span {a})) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hsq : ¬p^2 ∣ a) (h : O) :
    gaussRow a ha (p^6*h) = if p ∣ a then 0 else gaussRow a ha h := by
  unfold gaussRow
  rw [sexticGauss_pool_prime_mask a p ha hp hs hg hc hsq h]
  split_ifs <;> simp

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.sexticGauss_prime_dvd_zero
#print axioms OAI.SevenEighths.Record1252270103Source.sexticGauss_pool_prime_mask
#print axioms OAI.SevenEighths.Record1252270103Source.gaussRow_pool_prime_mask
