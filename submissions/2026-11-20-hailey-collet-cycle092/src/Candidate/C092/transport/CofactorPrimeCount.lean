/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uses the original OpenAI ideal-prime coprimality and the mathlib ideal norm. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.IdealFactorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
namespace QRH.Cycle092.CofactorPrime
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

/-- Distinct prime ideals dividing the true cofactor have a product dividing
that same cofactor. No squarefree norm or coprimality with the core is imposed. -/
theorem prime_product_dvd (E : Finset (Ideal O)) (B : Ideal O)
    (hprime : ∀ I∈E,Prime I) (hdiv : ∀ I∈E,I∣B) : (∏ I∈E,I)∣B := by
  apply Finset.prod_dvd_of_coprime _ hdiv
  intro I hI J hJ hne
  exact primeIdeal_coprime ⟨I,hprime I hI⟩ ⟨J,hprime J hJ⟩
    (fun h=>hne (congrArg Subtype.val h))

theorem divisor_norm_product_le (E : Finset (Ideal O)) {B : Ideal O}
    (hB : B ≠ 0) (hprime : ∀ I∈E,Prime I) (hdiv : ∀ I∈E,I∣B) :
    (∏ I∈E,(I.absNorm : ℝ)) ≤ (B.absNorm : ℝ) := by
  have hp := prime_product_dvd E B hprime hdiv
  have hn : (∏ I∈E,I.absNorm) ≤ B.absNorm := by
    have h := map_dvd Ideal.absNorm hp
    rw [map_prod] at h
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)) h
  exact_mod_cast hn

/-- Every active annular deleted prime pays one factor of its actual lower
norm; multiplicativity gives the load-bearing finite cardinality estimate. -/
theorem lower_norm_pow_card (E : Finset (Ideal O)) {B : Ideal O} {K : ℝ}
    (hB : B ≠ 0) (hK : 0 ≤ K) (hprime : ∀ I∈E,Prime I)
    (hdiv : ∀ I∈E,I∣B) (hlower : ∀ I∈E,K ≤ (I.absNorm : ℝ)) :
    K^E.card ≤ (B.absNorm : ℝ) := by
  calc
    _ = ∏ I∈E,K := by simp
    _ ≤ ∏ I∈E,(I.absNorm : ℝ) := Finset.prod_le_prod₀ (fun _ _=>hK) hlower
    _ ≤ _ := divisor_norm_product_le E hB hprime hdiv

theorem annular_card_log (E : Finset (Ideal O)) {B : Ideal O} {a P U A : ℝ}
    (hB : B ≠ 0) (ha : 0 < a) (hP : 1 < P) (hU : 0 < U)
    (hscale : (a⁻¹)^2 ≤ P) (hBcap : (B.absNorm : ℝ) ≤ U^A)
    (hprime : ∀ I∈E,Prime I) (hdiv : ∀ I∈E,I∣B)
    (hlower : ∀ I∈E,a*P ≤ (I.absNorm : ℝ)) :
    (E.card : ℝ) ≤ 2*A*Real.log U/Real.log P := by
  have hP0 := zero_lt_one.trans hP
  have hK0 := mul_pos ha hP0
  have ha₂ : 0 < a^2 := sq_pos_of_pos ha
  have hinv : 1/a^2 ≤ P := by simpa only [one_div,inv_pow] using hscale
  have hprod := (div_le_iff₀ ha₂).mp hinv
  have hsquare : P ≤ (a*P)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hP0.le]
  have hpow := lower_norm_pow_card E hB hK0.le hprime hdiv hlower
  have hlog := Real.log_le_log (pow_pos hK0 E.card) (hpow.trans hBcap)
  rw [Real.log_pow,Real.log_rpow hU] at hlog
  have hhalf := Real.log_le_log hP0 hsquare
  rw [Real.log_pow] at hhalf
  have hm := mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ E.card by positivity)
  norm_num only [Nat.cast_ofNat] at hhalf hm
  apply (le_div_iff₀ (Real.log_pos hP)).mpr
  nlinarith

end
end QRH.Cycle092.CofactorPrime
#print axioms QRH.Cycle092.CofactorPrime.annular_card_log
