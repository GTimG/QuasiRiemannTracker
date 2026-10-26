/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.HoleMass
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.ForwardEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.MassBounds

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentInductionEnergy
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem forwardDivisorMass_nonneg (b X₁ X₂ : ℝ) : 0 ≤ forwardDivisorMass b X₁ X₂ :=
  Finset.sum_nonneg (fun d _=>div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

theorem forwardDivisorMass_rankin (ε B U b X₁ X₂ : ℝ) (hε : 0<ε) (hB : 0≤B) (hU : 1≤U)
    (hcut : b^2*X₁*X₂≤U^B) :
    forwardDivisorMass b X₁ X₂ ≤
      (eulerBound 5 (1/2+ε/(B+1))+eulerBound 432 (1/2+ε/(B+1)))*U^ε := by
  apply le_trans _ (good_absolute_rankin_nonnegative ε B U hε hB hU
    (divisorPool (holePairPool b X₁ X₂)) (fun d hd=>divisorPool_hole_good hd)
      (fun d hd=>(divisorPool_norm_bound hd).trans hcut))
  apply Finset.sum_le_sum
  intro d hd
  exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (Real.sqrt_nonneg _)

theorem forward_energy_transfer {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (E : ℝ) (hEn : 0≤E)
    (δ B U : ℝ) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U) (hcut : b^2*X₁*X₂≤U^B)
    (hE : ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤X₁ → Y₂≤X₂ →
      energy η m A t W₁ W₂ S β P Y₁ Y₂ keep Φ K ≤ E) :
    squarefreeEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K ≤
      (holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  have h := forward_hole_energy_transfer η m A W₁ W₂ b S β P hP t X₁ X₂ hX₁ hX₂
    keep Φ K hK hΦ (holeDeletionMass^2*E) ?_
  · apply h.trans
    have hm := pow_le_pow_left₀ (forwardDivisorMass_nonneg b X₁ X₂)
      (forwardDivisorMass_rankin δ B U b X₁ X₂ hδ hB hU hcut) 2
    have he := mul_le_mul_of_nonneg_right hm (mul_nonneg (sq_nonneg holeDeletionMass) hEn)
    exact he.trans_eq (by ring)
  intro d hd
  have hdg := divisorPool_hole_good hd
  have hy₁ := shorten_positive hX₁ hdg.1
  have hy₂ := shorten_positive hX₂ hdg.2.1
  apply hole_energy_transfer η m A W₁ W₂ b hs₁ hs₂ S β P hP t _ _ hy₁.1 hy₂.1
    keep Φ K hK hΦ E
  intro D hD
  have hz₁ := shorten_positive hy₁.1 (subsetProduct_nonzero D.1)
  have hz₂ := shorten_positive hy₂.1 (subsetProduct_nonzero D.2)
  exact hE _ _ hz₁.1 hz₂.1 (hz₁.2.trans hy₁.2) (hz₂.2.trans hy₂.2)

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.forward_energy_transfer
