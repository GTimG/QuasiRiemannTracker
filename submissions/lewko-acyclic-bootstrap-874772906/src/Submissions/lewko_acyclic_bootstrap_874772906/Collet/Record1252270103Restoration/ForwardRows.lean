/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.SmallEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem forward_hole_plain_identity (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    squarefreePlainSum ψ W₁ W₂ b X₁ X₂ =
      ∑d∈divisorPool (holePairPool b X₁ X₂),(forwardKernel d.1 d.2:ℂ)*ψ (d.1*d.2)*
        ordinaryHolePlainSum ψ W₁ W₂ b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  rw [squarefreePlainSum_eq_hole_sum]
  have h := forward_finite_character_identity (holePairPool b X₁ X₂)
    (fun n hn=>⟨(holePairPool_good hn).1,(holePairPool_good hn).2.1⟩)
    ψ.toMonoidHom (pairProfile W₁ W₂ X₁ X₂)
  rw [expandedPairs_grouped (holePairPool b X₁ X₂) (fun d a =>
    (forwardKernel d.1 d.2:ℂ)*ψ.toMonoidHom (d.1*d.2)*ψ.toMonoidHom (a.1*a.2)*
      pairProfile W₁ W₂ X₁ X₂ (multiplyPair d a))] at h
  change (∑n∈holePairPool b X₁ X₂,(squarefreeIndicator (n.1*n.2):ℂ)*ψ (n.1*n.2)*
    pairProfile W₁ W₂ X₁ X₂ n)=_ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ordinaryHolePlainSum,Finset.mul_sum,residualPool_holePairPool hd]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pairProfile_multiply]
  change (forwardKernel d.1 d.2:ℂ)*ψ (d.1*d.2)*ψ (a.1*a.2)*pairProfile W₁ W₂ _ _ a = _
  ring

theorem forward_hole_positive_row {ι : Type*} [Fintype ι]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀ i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂ =
      ∑ d ∈ divisorPool (holePairPool b X₁ X₂),
        ((forwardKernel d.1 d.2:ℂ)*rowWeight η m A z t (d.1*d.2)/(Real.sqrt (pairNorm d):ℂ))*
        ordinaryHolePositiveSlotRow η m A z W₁ W₂ b S β P t
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  unfold squarefreePositiveSlotRow
  rw [forward_hole_plain_identity,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdg := divisorPool_hole_good hd
  have hn := pairNorm_pos hdg.1 hdg.2.1
  have hv : 0<X₁*X₂*∏ i,P i := mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  unfold ordinaryHolePositiveSlotRow
  have heq : (X₁/(Ideal.absNorm d.1:ℝ))*(X₂/(Ideal.absNorm d.2:ℝ))*∏ i,P i=
      (X₁*X₂*∏ i,P i)/pairNorm d := by unfold pairNorm; ring
  rw [heq,normalized_divisor_identity _ _ hv hn]
  ring

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.forward_hole_positive_row
