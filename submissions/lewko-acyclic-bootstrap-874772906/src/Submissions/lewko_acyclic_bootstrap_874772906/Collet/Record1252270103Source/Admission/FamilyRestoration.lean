/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Forward squarefree restoration on literal finite weighted row families. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.ForwardFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRetainedEnergy CenteredMomentAbsoluteEnergy
open Record1252270103Source QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O

lemma finite_weighted_energy {κ Row : Type*} (D : Finset κ) (rows : Finset Row)
    (w : κ→ℝ) (c f : κ→Row→ℂ) (weight : Row→ℝ) (E : ℝ)
    (hw : ∀d∈D,0≤w d) (hweight : ∀u∈rows,0≤weight u)
    (hc : ∀d∈D,∀u∈rows,‖c d u‖≤w d)
    (hf : ∀d∈D,(∑u∈rows,‖f d u‖^2*weight u)≤E) :
    (∑u∈rows,‖∑d∈D,c d u*f d u‖^2*weight u)≤(∑d∈D,w d)^2*E := by
  calc
    _ ≤ ∑u∈rows,(∑d∈D,w d)*(∑d∈D,w d*(‖f d u‖^2*weight u)) := by
      apply Finset.sum_le_sum
      intro u hu
      have h:=mul_le_mul_of_nonneg_right
        (norm_weighted_sum_sq D w (fun d=>c d u) (fun d=>f d u) hw
          (fun d hd=>hc d hd u hu)) (hweight u hu)
      simpa only [Finset.sum_mul,mul_assoc] using h
    _ = (∑d∈D,w d)*(∑d∈D,w d*(∑u∈rows,‖f d u‖^2*weight u)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ (∑d∈D,w d)*(∑d∈D,w d*E) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d hd=>
        mul_le_mul_of_nonneg_left (hf d hd) (hw d hd))) (Finset.sum_nonneg hw)
    _ = _ := by rw [←Finset.sum_mul];ring

variable {ι Row : Type*} [Fintype ι]

lemma hole_finite_family
    (rows : Finset Row) (η : Row→Character) (m A z : Row→O) (t weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (E : ℝ)
    (hE : ∀D∈mobiusPool,(∑u∈rows,‖positiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ S β P (t u) (X₁/Ideal.absNorm (mobiusPair D).1)
        (X₂/Ideal.absNorm (mobiusPair D).2)‖^2*weight u)≤E) :
    (∑u∈rows,‖ordinaryHolePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) X₁ X₂‖^2*weight u)≤holeDeletionMass^2*E := by
  simp_rw [hole_positive_row _ _ _ _ W₁ W₂ b hs₁ hs₂ S β P hP _ X₁ X₂ hX₁ hX₂]
  apply finite_weighted_energy mobiusPool rows
    (fun D=>(Real.sqrt (pairNorm (mobiusPair D)))⁻¹) _ _ weight E
    (fun D _=>inv_nonneg.mpr (Real.sqrt_nonneg _)) hw ?_ hE
  intro D hD u hu
  rw [norm_div,norm_mul]
  simp only [mobiusSign,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (rowWeight_norm_le_one_all _ _ _ _ _ _)
    (Real.sqrt_nonneg _)).trans_eq (one_div _)

/-- Arbitrary moving characters and numerators stay inside one finite family.
Every original weight is retained through both exact divisor expansions. -/
theorem forward_finite_family
    (rows : Finset Row) (η : Row→Character) (m A z : Row→O) (t weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (E : ℝ)
    (hE : ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤X₁ → Y₂≤X₂ →
      (∑u∈rows,‖positiveSlotRow (η u) (m u) (A u) (z u)
        W₁ W₂ S β P (t u) Y₁ Y₂‖^2*weight u)≤E) :
    (∑u∈rows,‖squarefreePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) X₁ X₂‖^2*weight u)≤
        (forwardDivisorMass b X₁ X₂)^2*(holeDeletionMass^2*E) := by
  simp_rw [forward_hole_positive_row _ _ _ _ W₁ W₂ b S β P hP _ X₁ X₂ hX₁ hX₂]
  apply finite_weighted_energy (divisorPool (holePairPool b X₁ X₂)) rows
    (fun d=>|(forwardKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d)) _ _ weight _
    (fun d _=>div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hw
  · intro d hd u hu
    rw [norm_div,norm_mul,Complex.norm_intCast,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (rowWeight_norm_le_one_all _ _ _ _ _ _))
      (Real.sqrt_nonneg _)
  · intro d hd
    have hdg:=divisorPool_hole_good hd
    have hy₁:=shorten_positive hX₁ hdg.1
    have hy₂:=shorten_positive hX₂ hdg.2.1
    apply hole_finite_family rows η m A z t weight hw W₁ W₂ b hs₁ hs₂ S β P hP
      _ _ hy₁.1 hy₂.1 E
    intro D hD
    have hz₁:=shorten_positive hy₁.1 (subsetProduct_nonzero D.1)
    have hz₂:=shorten_positive hy₂.1 (subsetProduct_nonzero D.2)
    exact hE _ _ hz₁.1 hz₂.1 (hz₁.2.trans hy₁.2) (hz₂.2.trans hy₂.2)

theorem forward_finite_family_rankin
    (rows : Finset Row) (η : Row→Character) (m A z : Row→O) (t weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (E : ℝ) (hE : 0≤E)
    (δ B U : ℝ) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U) (hcut : b^2*X₁*X₂≤U^B)
    (hraw : ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤X₁ → Y₂≤X₂ →
      (∑u∈rows,‖positiveSlotRow (η u) (m u) (A u) (z u)
        W₁ W₂ S β P (t u) Y₁ Y₂‖^2*weight u)≤E) :
    (∑u∈rows,‖squarefreePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) X₁ X₂‖^2*weight u)≤
      (holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
        eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  apply (forward_finite_family rows η m A z t weight hw W₁ W₂ b hs₁ hs₂ S β P hP
    X₁ X₂ hX₁ hX₂ E hraw).trans
  have hm:=pow_le_pow_left₀ (forwardDivisorMass_nonneg b X₁ X₂)
    (forwardDivisorMass_rankin δ B U b X₁ X₂ hδ hB hU hcut) 2
  exact (mul_le_mul_of_nonneg_right hm (mul_nonneg (sq_nonneg holeDeletionMass) hE)).trans_eq (by ring)

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.finite_weighted_energy
#print axioms QRH.Record1252270103Source.Admission.hole_finite_family
#print axioms QRH.Record1252270103Source.Admission.forward_finite_family
#print axioms QRH.Record1252270103Source.Admission.forward_finite_family_rankin
