/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform moving-puncture transfer at the original outer height. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.Height
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentLattice
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentSecondHeightFamily CenteredMomentTwist
open QRH.Record1252270103Reference
local notation "O" => HeckeFamily.O

/-- The constant precedes the character, puncture and all heights. The supplier
uses the same profiles, height and complete keep predicate on every shortening. -/
theorem fixed_mask_energy_transfer_height {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α) (bslot bound : α→ℝ) (hbound : ∀i∈F,0≤bound i)
    (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(η : Character)(R : Ideal O),R≠0 → ∀t : ℝ,
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ))(a b : ℝ),0<a → 0≤b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀(pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖β i I‖≤bound i) →
      (∀i∈F,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤bslot i*P i) →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
    ∀(keep : O→Prop),(∀z,keep z→z≠0) →
    ∀(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),0<K → (∀x,0≤(Φ x).re) → 0≤E →
      (∀G : Finset α,G⊆F → ∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤X₁ → Y₂≤X₂ →
        energy η (fixedBadMask*idealGenerator 1) 1 t W₁ W₂
          (fun i:G=>pool i) (fun (i:G) I=>β i I) (fun i:G=>P i)
          Y₁ Y₂ keep Φ K≤E) →
      energy η (fixedBadMask*idealGenerator R) 1 t W₁ W₂
        (fun i:F=>pool i) (fun (i:F) I=>β i I) (fun i:F=>P i) X₁ X₂ keep Φ K ≤
        C*(R.radical.absNorm:ℝ)^δ*E := by
  obtain ⟨C,hC,hm⟩ := fixed_mask_energy_transfer F bslot bound hbound δ hδ
  refine ⟨C,hC,?_⟩
  intro η R hR t W₁ W₂ a b ha hb hs₁ hs₂ pool β P hp hP hβ hs
    X₁ X₂ hX₁ hX₂ keep hkeep Φ K E hK hΦ hE hraw
  rw [energy_height η R hR t W₁ W₂ a b ha hs₁ hs₂ _ _ _
    (fun (i:F)=>hP i i.property) X₁ X₂ hX₁ hX₂ keep hkeep Φ K]
  apply hm η R hR _ _ a b ha hb
    ((normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t).trans hs₁)
    ((normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t).trans hs₂)
    pool (fun i=>heightCoefficient (β i) t) P hp hP
  · intro i hi I hI
    rw [heightCoefficient_norm _ t I (hp i hi I hI).ne_zero]
    exact hβ i hi I hI
  · intro i hi I hI hn
    exact hs i hi I hI (fun hz=>hn (by simp [heightCoefficient,hz]))
  · exact hX₁
  · exact hX₂
  · exact hkeep
  · exact hK
  · exact hΦ
  · exact hE
  · intro G hGF Y₁ Y₂ hY₁ hY₂ hYX₁ hYX₂
    have he := hraw G hGF Y₁ Y₂ hY₁ hY₂ hYX₁ hYX₂
    rw [energy_height η 1 one_ne_zero t W₁ W₂ a b ha hs₁ hs₂ _ _ _
      (fun (i:G)=>hP i (hGF i.property)) Y₁ Y₂ hY₁ hY₂ keep hkeep Φ K] at he
    exact he

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.fixed_mask_energy_transfer_height
