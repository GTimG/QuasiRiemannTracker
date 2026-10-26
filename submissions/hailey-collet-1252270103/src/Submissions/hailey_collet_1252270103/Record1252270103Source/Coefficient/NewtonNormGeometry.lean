/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual support and ideal norm geometry discharge the residual Newton counts. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedMarkedExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationCount
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open CenteredMomentAmplificationCount QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered QRH.Record1252270103KernelMass
open QRH.Record1252270103Restoration
local notation "O" => ActualEisensteinCubic.O

theorem ideal_pool_card_le_norm (P : Finset (Ideal O)) (I : Ideal O) (hI : I≠0)
    (hp : ∀p∈P,Prime p) (Z ell B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hupper : (I.absNorm:ℝ)≤Z^B) :
    ((idealDividingPool P I).card:ℝ)≤B/ell :=
  indexed_large_prime_divisor_count (idealDividingPool P I) (fun p=>p)
    (fun _ _ _ _ h=>h) (fun p h=>hp p (Finset.mem_filter.mp h).1) I hI
    (fun p h=>(Finset.mem_filter.mp h).2) Z ell B hZ hell
    (fun p h=>hlower p (Finset.mem_filter.mp h).1) hupper

theorem frozen_profile_plain_norm (W₁ W₂ : ℝ→ℂ) (A₁ A₂ : Ideal O)
    (b X₁ X₂ Y₁ Y₂ : ℝ) (hb : 0≤b) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (heq : Y₁*Y₂=X₁*X₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (n : IdealPair) (hne : frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0) :
    ((n.1*n.2).absNorm:ℝ)≤b^2*(X₁*X₂) := by
  have hc := ((frozenProfile_nonzero_iff W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n).mp hne).2
  have hbnd (U₁ U₂ : ℝ) (hU₁ : 0<U₁) (hU₂ : 0<U₂)
      (h : pairProfile W₁ W₂ U₁ U₂ n≠0) : ((n.1*n.2).absNorm:ℝ)≤b^2*(U₁*U₂) := by
    obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp h
    have hn₁ := (div_le_iff₀ hU₁).mp (hs₁ h₁)
    have hn₂ := (div_le_iff₀ hU₂).mp (hs₂ h₂)
    rw [map_mul,Nat.cast_mul]
    exact (mul_le_mul hn₁ hn₂ (Nat.cast_nonneg _) (mul_nonneg hb hU₁.le)).trans_eq (by ring)
  by_cases hx : pairProfile W₁ W₂ X₁ X₂ n=0
  · have hy : pairProfile W₁ W₂ Y₁ Y₂ n≠0 := by
      intro hy
      exact hc (by simp only [centeredProfile,hx,hy,sub_self])
    simpa only [heq] using hbnd Y₁ Y₂ hY₁ hY₂ hy
  · exact hbnd X₁ X₂ hX₁ hX₂ hx

theorem frozen_profile_newton_count (P : Finset (Ideal O)) (depth : ℕ)
    (hp : ∀p∈P,Prime p) (Z ell B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hdepth : B/ell≤depth)
    (W₁ W₂ : ℝ→ℂ) (A₁ A₂ : Ideal O) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (hb : 0≤b) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (heq : Y₁*Y₂=X₁*X₂) (hupper : b^2*(X₁*X₂)≤Z^B)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (n : IdealPair) (hn : n∈commonPool b X₁ X₂ Y₁ Y₂)
    (hne : frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0) :
    (idealDividingPool P (n.1*n.2)).card≤depth := by
  have hg := holePairPool_good hn
  have hnorm := frozen_profile_plain_norm W₁ W₂ A₁ A₂ b X₁ X₂ Y₁ Y₂
    hb hX₁ hX₂ hY₁ hY₂ heq hs₁ hs₂ n hne
  have hc := ideal_pool_card_le_norm P (n.1*n.2) (mul_ne_zero hg.1 hg.2.1) hp
    Z ell B hZ hell hlower (hnorm.trans hupper)
  exact_mod_cast hc.trans hdepth

theorem actual_newton_budget (P : Finset (Ideal O)) (D : Ideal O) (hD : D≠0)
    (depth : ℕ) (hp : ∀p∈P,Prime p) (Z ell BD : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hupper : (D.absNorm:ℝ)≤Z^BD)
    (hsize : 2*(BD/ell+depth+1)≤P.card) :
    2*((idealDividingPool P D).card+depth+1:ℝ)≤P.card := by
  have hc := ideal_pool_card_le_norm P D hD hp Z ell BD hZ hell hlower hupper
  linarith

end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.frozen_profile_newton_count
#print axioms OAI.SevenEighths.Record1252270103Source.actual_newton_budget
