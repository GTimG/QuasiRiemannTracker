/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterCoefficients
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.IdealEuler

/-! Reconstruct the genuine two extracted ideals and the scale-independent
signed coefficients of the complete numerator expansion. -/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

lemma eulerVariable_eq_normWeight (ψ : Character) (P : PrimeIdeal) (s : ℂ) :
    eulerVariable ψ P s=idealCoeff ψ P.val*IdealEuler.normWeight s P.val := by
  change idealCoeff ψ P.val*(Ideal.absNorm P.val : ℂ)^(-s)=
    idealCoeff ψ P.val*(if P.val=0 then 0 else (Ideal.absNorm P.val : ℂ)^(-s))
  rw [ite_eq_right P.property.ne_zero]

def goodCoefficient (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal) (k : GoodIndex bad) : ℂ :=
  ∏ P : k.1,h3Sign (k.2 P)*idealCoeff ψ₁ P.val.val.val^(h3Exponent (k.2 P)).1*
    idealCoeff ψ₂ P.val.val.val^(h3Exponent (k.2 P)).2

def badCoefficient (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : BadIndex bad allowed) : ℂ :=
  ∏ P : bad,idealCoeff ψ₁ P.val.val^(k P).val.1*idealCoeff ψ₂ P.val.val^(k P).val.2

def fullCoefficient (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : FullIndex bad allowed) : ℂ :=
  badCoefficient ψ₁ ψ₂ bad allowed k.1*goodCoefficient ψ₁ ψ₂ bad k.2

lemma goodSeriesTerm_coefficient (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (s₁ s₂ : ℂ) (k : GoodIndex bad) :
    goodSeriesTerm ψ₁ ψ₂ bad s₁ s₂ k =goodCoefficient ψ₁ ψ₂ bad k*
      IdealEuler.normWeight s₁ (goodIdeal₁ bad k)*IdealEuler.normWeight s₂ (goodIdeal₂ bad k) := by
  simp only [goodSeriesTerm,primeTerm,h3Term,eulerVariable_eq_normWeight,mul_pow,
    goodCoefficient,goodIdeal₁,goodIdeal₂,map_prod,map_pow]
  rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  ring

lemma badSeriesTerm_coefficient (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) (k : BadIndex bad allowed) :
    badSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k =badCoefficient ψ₁ ψ₂ bad allowed k*
      IdealEuler.normWeight s₁ (badIdeal₁ bad allowed k)*IdealEuler.normWeight s₂ (badIdeal₂ bad allowed k) := by
  simp only [badSeriesTerm,eulerVariable_eq_normWeight,mul_pow,badCoefficient,
    badIdeal₁,badIdeal₂,map_prod,map_pow]
  rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  ring

/-- Exact bivariate coefficient identity, including both extracted exceptional
ideals, both good-prime ideals, and all original character coefficients. -/
theorem fullSeriesTerm_coefficient (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (s₁ s₂ : ℂ) (k : FullIndex bad allowed) :
    fullSeriesTerm ψ₁ ψ₂ bad allowed s₁ s₂ k =fullCoefficient ψ₁ ψ₂ bad allowed k*
      IdealEuler.normWeight s₁ (fullIdeal₁ bad allowed k)*
      IdealEuler.normWeight s₂ (fullIdeal₂ bad allowed k) := by
  rw [fullSeriesTerm,goodSeriesTerm_coefficient,badSeriesTerm_coefficient]
  simp only [fullCoefficient,fullIdeal₁,fullIdeal₂,map_mul]
  ring

lemma normWeight_critical (I : Ideal O) (hI : I ≠ 0) :
    ‖IdealEuler.normWeight (2/5 : ℂ) I‖=(Ideal.absNorm I : ℝ)^(-(2/5 : ℝ)) := by
  simp only [IdealEuler.normWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
    CubicEisenstein.fullIdealWeight,ite_eq_right hI]
  change ‖((Ideal.absNorm I : ℝ) : ℂ)^(-(2/5 : ℂ))‖ = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))))]
  norm_num

/-- The actual coefficient mass at the exact critical exponents (2/5,2/5).
This is the weighted ℓ¹ statement needed for the proposed convolution proof. -/
theorem fullCoefficient_weighted_summable (ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) :
    Summable (fun k : FullIndex bad allowed => ‖fullCoefficient ψ₁ ψ₂ bad allowed k‖*
      ((Ideal.absNorm (fullIdeal₁ bad allowed k) : ℝ)*
        (Ideal.absNorm (fullIdeal₂ bad allowed k) : ℝ))^(-(2/5 : ℝ))) := by
  apply (fullSeries_summable_norm ψ₁ ψ₂ bad allowed (2/5 : ℂ) (2/5 : ℂ)
    (by norm_num) (by norm_num)).congr
  intro k
  rw [fullSeriesTerm_coefficient,norm_mul,norm_mul,
    normWeight_critical _ (fullIdeal₁_ne_zero bad allowed k),
    normWeight_critical _ (fullIdeal₂_ne_zero bad allowed k),
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

end
end QRH.Cycle092.SignedCenter
