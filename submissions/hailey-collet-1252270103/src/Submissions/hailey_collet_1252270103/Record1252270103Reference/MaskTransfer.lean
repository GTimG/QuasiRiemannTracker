/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed whole-column punctures are expanded by OpenAI/math's finite common-mask
Möbius and marked-slot deletion, retaining the original positive radial filter. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.InductionEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Reference
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentLattice CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma energy_eq_masked_radial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (hkeep : ∀z,keep z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η (fixedBadMask*idealGenerator R) 1 0 W₁ W₂ pool β P X₁ X₂ keep Φ K =
      radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false W₁ X₁ 0 0 *
        polynomial (excluded (naturalCharacter η z) R) false W₂ X₂ 0 0 *
        ∏i,naturalSlot (excluded (naturalCharacter η z) R) (pool i) (β i) (P i)) keep Φ K := by
  have h₁ : normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) 0 = W₁ := by
    ext x
    simp [normPowerProfile_apply]
  have h₂ : normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) 0 = W₂ := by
    ext x
    simp [normPowerProfile_apply]
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · simp only [hz,ite_true]
    have he := original_positive_normalized (naturalRow η z (hkeep z hz)) R hR
      W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
      pool β P hP 0 X₁ X₂ hX₁ hX₂
    rw [h₁,h₂] at he
    rw [he,naturalCharacter_eq η z (hkeep z hz)]
    have hc (i : ι) : CenteredMomentCommonMaskEnergy.heightCoefficient (β i) 0 = β i := by
      funext I
      simp [CenteredMomentCommonMaskEnergy.heightCoefficient]
    simp only [hc,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul]
  · simp only [hz,ite_false]

lemma excluded_one_coefficient (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I = idealCoeff χ I := by
  rw [excluded_ideal χ 1 one_ne_zero I]
  simp only [isCoprime_one_right,ite_true]

lemma excluded_one_polynomial (χ : Character) (W : ℝ→ℂ) (X : ℝ) :
    polynomial (excluded χ 1) false W X 0 0 = polynomial χ false W X 0 0 := by
  unfold polynomial summand coefficient
  simp only [Bool.false_eq_true,ite_false,excluded_one_coefficient]


lemma energy_eq_unit_radial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (hkeep : ∀z,keep z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η (fixedBadMask*idealGenerator 1) 1 0 W₁ W₂ pool β P X₁ X₂ keep Φ K =
      radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0 *
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0 *
        ∏i,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i)) keep Φ K := by
  rw [energy_eq_masked_radial η 1 one_ne_zero W₁ W₂ a b ha hs₁ hs₂ pool β P hP
    X₁ X₂ hX₁ hX₂ keep hkeep Φ K]
  simp only [excluded_one_polynomial,naturalSlot,excluded_one_coefficient]

/-- Finite whole-column puncture transfer. Every surviving marked subset and
all positive shortened ordinary factors remain explicit in the hypothesis. -/
theorem fixed_mask_energy_transfer {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset α) (bslot bound : α→ℝ) (hbound : ∀i∈F,0≤bound i)
    (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(η : Character)(R : Ideal O),R≠0 →
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
        energy η (fixedBadMask*idealGenerator 1) 1 0 W₁ W₂
          (fun i:G=>pool i) (fun (i:G) I=>β i I) (fun i:G=>P i)
          Y₁ Y₂ keep Φ K≤E) →
      energy η (fixedBadMask*idealGenerator R) 1 0 W₁ W₂
        (fun i:F=>pool i) (fun (i:F) I=>β i I) (fun i:F=>P i) X₁ X₂ keep Φ K ≤
        C*(R.radical.absNorm:ℝ)^δ*E := by
  obtain ⟨C,hC,hshared⟩ := CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy
    F bslot bound hbound δ hδ
  refine ⟨C,hC,?_⟩
  intro η R hR W₁ W₂ a b ha hb hs₁ hs₂ pool β P hp hP hβ hsupport
    X₁ X₂ hX₁ hX₂ keep hkeep Φ K E hK hΦ hE hraw
  rw [energy_eq_masked_radial η R hR W₁ W₂ a b ha hs₁ hs₂
    (fun i:F=>pool i) (fun (i:F) I=>β i I) (fun i:F=>P i)
    (fun i=>hP i i.property) X₁ X₂ hX₁ hX₂ keep hkeep Φ K]
  have hh := hshared (CompletedGauss.primeSupport R) (support_prime R)
    (naturalCharacter η) W₁ W₂ X₁ X₂ a b a b pool β P keep Φ K E
    hX₁ hX₂ hb hb hs₁ hs₂ hp hP hβ hsupport hK (fun z=>hΦ _) hE ?_
  · rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical R hR] at hh
    have hprod (z : O) := Finset.prod_coe_sort F
      (fun i=>naturalSlot (excluded (naturalCharacter η z) R) (pool i) (β i) (P i))
    change radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (naturalCharacter η z) R) false W₂ X₂ 0 0 *
      ∏i∈F,naturalSlot (excluded (naturalCharacter η z) R) (pool i) (β i) (P i)) keep Φ K ≤ _ at hh
    simp_rw [←hprod] at hh
    exact hh
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        1≤(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    have hy₁ : 0<X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ) := div_pos hX₁ (by linarith [hn D₁ hD₁])
    have hy₂ : 0<X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ) := div_pos hX₂ (by linarith [hn D₂ hD₂])
    have he := hraw (F\J) Finset.sdiff_subset _ _ hy₁ hy₂
      (div_le_self hX₁.le (hn D₁ hD₁)) (div_le_self hX₂.le (hn D₂ hD₂))
    rw [energy_eq_unit_radial η W₁ W₂ a b ha hs₁ hs₂ _ _ _
      (fun (i : ↥(F\J))=>hP i (Finset.mem_sdiff.mp i.property).1) _ _ hy₁ hy₂ keep hkeep Φ K] at he
    have hprod (z : O) := Finset.prod_coe_sort (F\J)
      (fun i=>naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
    simp_rw [hprod] at he
    exact he

end
end QRH.Record1252270103Reference
#print axioms QRH.Record1252270103Reference.energy_eq_masked_radial
#print axioms QRH.Record1252270103Reference.excluded_one_polynomial

#print axioms QRH.Record1252270103Reference.fixed_mask_energy_transfer
