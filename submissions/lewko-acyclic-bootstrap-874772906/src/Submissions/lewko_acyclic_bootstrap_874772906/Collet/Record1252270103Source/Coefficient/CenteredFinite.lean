/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Both centered rectangles use one actual finite divisor pool. Compact support
justifies zero padding, so the centered difference survives the h expansion. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.DivisorCentered
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.ForwardRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.HoleRows

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open CenteredMomentSourceMass HeckeFamily
local notation "O" => HeckeFamily.O

theorem pairProfile_support_mem (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (n : IdealPair) (hn : n.1≠0 ∧ n.2≠0) (hf : pairProfile W₁ W₂ X₁ X₂ n≠0) :
    n∈plainPairPool b X₁ X₂ := by
  obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp hf
  exact Finset.mem_product.mpr ⟨(mem_idealBall _ _).mpr ⟨hn.1,(div_le_iff₀ hX₁).mp (hs₁ h₁)⟩,
    (mem_idealBall _ _).mpr ⟨hn.2,(div_le_iff₀ hX₂).mp (hs₂ h₂)⟩⟩

theorem plainPairPool_mono (b X₁ X₂ T₁ T₂ : ℝ) (hb : 0≤b) (h₁ : X₁≤T₁) (h₂ : X₂≤T₂) :
    plainPairPool b X₁ X₂⊆plainPairPool b T₁ T₂ := by
  intro n hn
  obtain ⟨hn₁,hn₂⟩ := Finset.mem_product.mp hn
  obtain ⟨hz₁,hN₁⟩ := (mem_idealBall _ _).mp hn₁
  obtain ⟨hz₂,hN₂⟩ := (mem_idealBall _ _).mp hn₂
  exact Finset.mem_product.mpr ⟨(mem_idealBall _ _).mpr ⟨hz₁,hN₁.trans (mul_le_mul_of_nonneg_left h₁ hb)⟩,
    (mem_idealBall _ _).mpr ⟨hz₂,hN₂.trans (mul_le_mul_of_nonneg_left h₂ hb)⟩⟩

theorem holePairPool_mono (b X₁ X₂ T₁ T₂ : ℝ) (hb : 0≤b) (h₁ : X₁≤T₁) (h₂ : X₂≤T₂) :
    holePairPool b X₁ X₂⊆holePairPool b T₁ T₂ :=
  Finset.filter_subset_filter _ (plainPairPool_mono b X₁ X₂ T₁ T₂ hb h₁ h₂)

theorem pair_sum_pad (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ T₁ T₂ : ℝ)
    (hb : 0≤b) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (h₁ : X₁≤T₁) (h₂ : X₂≤T₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (κ : IdealPair→ℂ) :
    (∑n∈plainPairPool b X₁ X₂,κ n*pairProfile W₁ W₂ X₁ X₂ n)=
      ∑n∈plainPairPool b T₁ T₂,κ n*pairProfile W₁ W₂ X₁ X₂ n := by
  apply Finset.sum_subset (plainPairPool_mono b X₁ X₂ T₁ T₂ hb h₁ h₂)
  intro n hn hn'
  have hz : pairProfile W₁ W₂ X₁ X₂ n=0 := by
    by_contra hf
    exact hn' (pairProfile_support_mem W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ n (plainPairPool_nonzero hn) hf)
  rw [hz,mul_zero]

theorem hole_pair_sum_pad (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ T₁ T₂ : ℝ)
    (hb : 0≤b) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (h₁ : X₁≤T₁) (h₂ : X₂≤T₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (κ : IdealPair→ℂ) :
    (∑n∈holePairPool b X₁ X₂,κ n*pairProfile W₁ W₂ X₁ X₂ n)=
      ∑n∈holePairPool b T₁ T₂,κ n*pairProfile W₁ W₂ X₁ X₂ n := by
  apply Finset.sum_subset (holePairPool_mono b X₁ X₂ T₁ T₂ hb h₁ h₂)
  intro n hn hn'
  have hz : pairProfile W₁ W₂ X₁ X₂ n=0 := by
    by_contra hf
    exact hn' (Finset.mem_filter.mpr ⟨pairProfile_support_mem W₁ W₂ b X₁ X₂ hX₁ hX₂
      hs₁ hs₂ n (plainPairPool_nonzero (Finset.mem_filter.mp hn).1) hf,(Finset.mem_filter.mp hn).2⟩)
  rw [hz,mul_zero]

theorem forward_hole_common_pool (ψ : Ideal O→*₀ℂ) (W₁ W₂ : ℝ→ℂ)
    (b X₁ X₂ T₁ T₂ : ℝ) (hb : 0≤b) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (h₁ : X₁≤T₁) (h₂ : X₂≤T₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b) :
    squarefreePlainSum ψ W₁ W₂ b X₁ X₂=
      ∑d∈divisorPool (holePairPool b T₁ T₂),(forwardKernel d.1 d.2:ℂ)*ψ (d.1*d.2)*
        ordinaryHolePlainSum ψ W₁ W₂ b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  rw [squarefreePlainSum_eq_hole_sum,
    hole_pair_sum_pad W₁ W₂ b X₁ X₂ T₁ T₂ hb hX₁ hX₂ h₁ h₂ hs₁ hs₂]
  have h:=forward_finite_character_identity (holePairPool b T₁ T₂)
    (fun n hn=>⟨(holePairPool_good hn).1,(holePairPool_good hn).2.1⟩)
    ψ.toMonoidHom (pairProfile W₁ W₂ X₁ X₂)
  rw [expandedPairs_grouped (holePairPool b T₁ T₂) (fun d a=>
    (forwardKernel d.1 d.2:ℂ)*ψ.toMonoidHom (d.1*d.2)*ψ.toMonoidHom (a.1*a.2)*
      pairProfile W₁ W₂ X₁ X₂ (multiplyPair d a))] at h
  change (∑n∈holePairPool b T₁ T₂,(squarefreeIndicator (n.1*n.2):ℂ)*ψ (n.1*n.2)*
    pairProfile W₁ W₂ X₁ X₂ n)=_ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro d hd
  have hdg:=divisorPool_hole_good hd
  have hdn₁ : 0<(Ideal.absNorm d.1:ℝ):=lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hdg.1)
  have hdn₂ : 0<(Ideal.absNorm d.2:ℝ):=lt_of_lt_of_le zero_lt_one (ideal_norm_one_le hdg.2.1)
  rw [residualPool_holePairPool hd]
  simp_rw [pairProfile_multiply]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  congr 2
  unfold ordinaryHolePlainSum
  symm
  exact hole_pair_sum_pad W₁ W₂ b _ _ _ _ hb (div_pos hX₁ hdn₁) (div_pos hX₂ hdn₂)
    (div_le_div_of_nonneg_right h₁ hdn₁.le) (div_le_div_of_nonneg_right h₂ hdn₂.le)
    hs₁ hs₂ (fun a=>ψ (a.1*a.2))

theorem forward_centered_common_pool (ψ : Ideal O→*₀ℂ) (W₁ W₂ : ℝ→ℂ)
    (b X₁ X₂ Y₁ Y₂ : ℝ) (hb : 0≤b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b) :
    squarefreePlainSum ψ W₁ W₂ b X₁ X₂-squarefreePlainSum ψ W₁ W₂ b Y₁ Y₂=
      ∑d∈divisorPool (holePairPool b (max X₁ Y₁) (max X₂ Y₂)),
        (forwardKernel d.1 d.2:ℂ)*ψ (d.1*d.2)*
          (ordinaryHolePlainSum ψ W₁ W₂ b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)-
           ordinaryHolePlainSum ψ W₁ W₂ b (Y₁/Ideal.absNorm d.1) (Y₂/Ideal.absNorm d.2)) := by
  rw [forward_hole_common_pool ψ W₁ W₂ b X₁ X₂ (max X₁ Y₁) (max X₂ Y₂) hb hX₁ hX₂
      (le_max_left _ _) (le_max_left _ _) hs₁ hs₂,
    forward_hole_common_pool ψ W₁ W₂ b Y₁ Y₂ (max X₁ Y₁) (max X₂ Y₂) hb hY₁ hY₂
      (le_max_right _ _) (le_max_right _ _) hs₁ hs₂,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.forward_centered_common_pool
