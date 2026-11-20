/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairCoefficient
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Mask

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeCancellation
local notation "O" => HeckeFamily.O

def divisorProfileTerm (χ : Character) (D : Ideal O) (W : ℝ → ℂ) (x : ℝ) (I : Ideal O) : ℂ :=
  if I ≠ 0 ∧ D ∣ I then idealCoeff χ (idealQuotient I D)*W ((Ideal.absNorm I : ℝ)/x) else 0

lemma divisorProfileTerm_summable (χ : Character) (D : Ideal O) (W : ℝ → ℂ)
    (b x : ℝ) (hx : 0 < x) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (divisorProfileTerm χ D W x) := by
  have h := CenteredMomentMask.annular_ideal_sum_summable
    (fun I => if I ≠ 0 ∧ D ∣ I then idealCoeff χ (idealQuotient I D) else 0) W b x hx hs
  apply h.congr
  intro I
  unfold divisorProfileTerm
  split_ifs <;> simp

lemma divisorProfileTerm_tsum (χ : Character) (D : Ideal O) (hD : D ≠ 0)
    (W : ℝ → ℂ) (x : ℝ) :
    (∑' I : Ideal O,divisorProfileTerm χ D W x I)=
      idealSum χ W (x/(Ideal.absNorm D : ℝ)) := by
  have he (I : Ideal O) : divisorProfileTerm χ D W x I=
      if D ∣ I then (if I=0 then 0 else idealCoeff χ (idealQuotient I D)*W ((Ideal.absNorm I : ℝ)/x)) else 0 := by
    by_cases hi : I=0 <;> by_cases hd : D ∣ I <;> simp only [divisorProfileTerm,ne_eq,hi,hd,
      not_true_eq_false,not_false_eq_true,false_and,true_and,ite_true,ite_false,ite_self]
  simp_rw [he]
  rw [CenteredMomentMask.tsum_ideal_divisible D hD]
  unfold idealSum
  apply tsum_congr
  intro A
  by_cases hA : A=0
  · subst A
    simp only [mul_zero,ite_true,map_zero,zero_mul]
  · rw [ite_eq_right (mul_ne_zero hD hA),idealQuotient_mul_cancel D A hD hA]
    rw [map_mul,Nat.cast_mul]
    have hn : (Ideal.absNorm D : ℝ) ≠ 0 := by
      exact_mod_cast (show Ideal.absNorm D ≠ 0 from fun he => hD (Ideal.absNorm_eq_zero_iff.mp he))
    congr 2
    rw [div_div_eq_mul_div]
    ring

lemma idealResidualCoefficient_profile (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed)
    (W₁ W₂ : ℝ → ℂ) (x y : ℝ) (I J : Ideal O) :
    idealResidualCoefficient χ₁ χ₂ bad allowed I J k*
      W₁ ((Ideal.absNorm I : ℝ)/x)*W₂ ((Ideal.absNorm J : ℝ)/y)=
      divisorProfileTerm χ₁ (correctedIdeal₁ bad allowed k) W₁ x I*
        divisorProfileTerm χ₂ (correctedIdeal₂ bad allowed k) W₂ y J := by
  by_cases hi : I=0 <;> by_cases hj : J=0 <;>
    by_cases hd₁ : correctedIdeal₁ bad allowed k ∣ I <;>
    by_cases hd₂ : correctedIdeal₂ bad allowed k ∣ J <;>
    simp only [idealResidualCoefficient,divisorProfileTerm,ne_eq,hi,hj,hd₁,hd₂,
      not_true_eq_false,not_false_eq_true,false_and,true_and,and_false,and_true,ite_true,ite_false,
      zero_mul,mul_zero] <;> ring

lemma idealResidualCoefficient_profile_tsum (χ₁ χ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (k : CorrectedIndex bad allowed)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    (∑' p : Ideal O×Ideal O,physicalPairTerm
      (fun I J => idealResidualCoefficient χ₁ χ₂ bad allowed I J k) W₁ W₂ x y p)=
      idealSum χ₁ W₁ (x/(Ideal.absNorm (correctedIdeal₁ bad allowed k) : ℝ))*
        idealSum χ₂ W₂ (y/(Ideal.absNorm (correctedIdeal₂ bad allowed k) : ℝ)) := by
  simp only [physicalPairTerm,idealResidualCoefficient_profile]
  have h₁ := divisorProfileTerm_summable χ₁ (correctedIdeal₁ bad allowed k) W₁ b₁ x hx hs₁
  have h₂ := divisorProfileTerm_summable χ₂ (correctedIdeal₂ bad allowed k) W₂ b₂ y hy hs₂
  rw [←tsum_mul_tsum_of_summable_norm h₁.norm h₂.norm]
  rw [divisorProfileTerm_tsum χ₁ _ (correctedIdeal₁_ne_zero bad allowed k),
    divisorProfileTerm_tsum χ₂ _ (correctedIdeal₂_ne_zero bad allowed k)]

#print axioms idealResidualCoefficient_profile_tsum
end
end QRH.Cycle092.SignedCenter
