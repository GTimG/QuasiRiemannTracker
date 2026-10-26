/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.SmallFibers

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentHeckeHeight
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem small_plain_identity (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    (∑n∈plainPairPool b X₁ X₂,ψ (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n) =
      ∑d∈smallPool (plainPairPool b X₁ X₂),ψ (d.1*d.2)*
        ordinaryHolePlainSum ψ W₁ W₂ b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  rw [small_sum_reindex _ (fun n hn=>plainPairPool_nonzero hn),
    smallExpanded_grouped _ (fun d a=>ψ ((multiplyPair d a).1*(multiplyPair d a).2)*
      pairProfile W₁ W₂ X₁ X₂ (multiplyPair d a))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ordinaryHolePlainSum,Finset.mul_sum,smallResidualPool_eq_hole hd]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pairProfile_multiply]
  have h : ψ ((multiplyPair d a).1*(multiplyPair d a).2)=ψ (d.1*d.2)*ψ (a.1*a.2) := by
    have he : (multiplyPair d a).1*(multiplyPair d a).2=(d.1*d.2)*(a.1*a.2) := by
      unfold multiplyPair;dsimp;ring
    rw [he,map_mul]
  rw [h,mul_assoc]

theorem small_positive_row {ι : Type*} [Fintype ι]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ =
      ∑d∈smallPool (plainPairPool b X₁ X₂),
        (rowWeight η m A z t (d.1*d.2)/(Real.sqrt (pairNorm d):ℂ))*
          ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  unfold positiveSlotRow
  rw [ordinary_product_eq_pair_sum η m A z t W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂,
    small_plain_identity,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdg := smallPool_nonzero hd
  have hn := pairNorm_pos hdg.1 hdg.2
  have hv : 0<X₁*X₂*∏i,P i := mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  unfold ordinaryHolePositiveSlotRow
  have heq : (X₁/(Ideal.absNorm d.1:ℝ))*(X₂/(Ideal.absNorm d.2:ℝ))*∏i,P i=
    (X₁*X₂*∏i,P i)/pairNorm d := by unfold pairNorm;ring
  rw [heq,normalized_divisor_identity _ _ hv hn]
  ring

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.small_positive_row
