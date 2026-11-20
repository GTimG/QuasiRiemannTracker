/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.SmallCoreEnergy

/-! Actual-energy monotonicity needed to join native, near and tiny radii with
one mesh and one smaller positive response buffer. No new moment premise. -/
set_option autoImplicit false
namespace QRH.Cycle092.SmallCore
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open QRH.Cycle092.WholeSlot
open HeckeFamily CenteredMomentWholeSlotDeletion CenteredMomentSlotNormalization
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

theorem lowRows_mono_buffer {Slot : Type*} (J : Finset Slot)
    (η : Character) (m A z : O) (t U e C buffer buffer' : ℝ) (w : Slot→ℝ)
    (pool : Slot→Finset (Ideal O)) (coeff : Slot→Ideal O→ℂ) (P : Slot→ℝ)
    (hU : 1 ≤ U) (hC : 0 ≤ C) (hb : buffer ≤ buffer') :
    LowRows J η m A t U e (C*U^buffer) w pool coeff P z →
      LowRows J η m A t U e (C*U^buffer') w pool coeff P z := by
  intro hz i hi
  have hm := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hb) hC
  exact (hz i hi).trans (mul_le_mul_of_nonneg_right hm
    (Real.rpow_nonneg (zero_le_one.trans hU) _))

/-- Monotonicity on the genuine original positive energy, with summability
discharged by the actual finite ordinary and slot polynomials. -/
theorem energy_mono_keep {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (η : Character) (m A : O) (t : ℝ) {a b : ℝ} (p : Profiles a b)
    (pool : Slot→Finset (Ideal O)) (coeff : Slot→Ideal O→ℂ) (P : Slot→ℝ)
    (X₁ X₂ : ℝ) (keep keep' : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i,0 ≤ P i) (hK : 0 < K)
    (hΦ : ∀ x,0 ≤ (Φ x).re) (hk : ∀ z,keep z→keep' z) :
    energy η m A t (p.profile 0) (p.profile 1) pool coeff P X₁ X₂ keep Φ K ≤
      energy η m A t (p.profile 0) (p.profile 1) pool coeff P X₁ X₂ keep' Φ K := by
  have hs (f : O→Prop) := subset_summable (Finset.univ : Finset Slot)
    η m A t (p.profile 0) (p.profile 1) pool coeff P X₁ X₂ b b hX₁ hX₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2) f Φ K hK hP
  have hs₀ := hs keep
  have hs₁ := hs keep'
  simp_rw [selectedProduct_univ η m A _ _ _ pool coeff P t X₁ X₂
    (mul_pos hX₁ hX₂).le hP] at hs₀ hs₁
  unfold energy
  apply hs₀.tsum_le_tsum _ hs₁
  intro z
  by_cases hz : keep z
  · simp only [hz,hk z hz,↓reduceIte]
    exact le_rfl
  · simp only [hz,↓reduceIte]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl

end
end QRH.Cycle092.SmallCore
#print axioms QRH.Cycle092.SmallCore.energy_mono_keep
