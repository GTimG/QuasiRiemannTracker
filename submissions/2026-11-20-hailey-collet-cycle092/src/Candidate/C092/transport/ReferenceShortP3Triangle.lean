/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original independent-column signed rectangle and exact equal-volume root
triangle. All common marks and complex outside phases are retained. -/
import Candidate.C092.transport.ReferenceShortP3Subsets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceShortP3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
local notation "O" => HeckeFamily.O

def pairRowOn {ι : Type} (T : Finset ι) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow) : ℂ :=
  (original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁ *
    original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂)*∏ i∈T,mark i u

def signedPairOn {ι : Type} (T : Finset ι) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow) : ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹ *
    (rowTwistedSum η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁ *
      rowTwistedSum η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂ -
     rowTwistedSum η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ Y₁ *
      rowTwistedSum η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ Y₂)*∏ i∈T,mark i u

def signedPairEnergyOn {ι : Type} (T : Finset ι) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (mark : ι→FreeRow→ℂ) : ℝ :=
  ∑ u∈s,‖signedPairOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark u‖^2

theorem pairRow_energy {ι : Type} [Fintype ι] (T : Finset ι) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ) (mark : ι→FreeRow→ℂ) :
    (∑ u∈s,‖pairRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u‖^2) =
      finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  unfold pairRowOn finiteEnergyOn
  apply Finset.sum_congr rfl
  intro u hu
  rw [norm_mul,norm_mul,norm_prod,mul_pow,mul_pow,←Finset.prod_pow]

theorem pairRow_sub_eq_signed {ι : Type} (T : Finset ι) (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ)
    (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ) (mark : ι→FreeRow→ℂ) (u : FreeRow)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hprod : Y₁*Y₂ = X₁*X₂) :
    pairRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark u -
      pairRowOn T η₁ η₂ W₁ W₂ t₁ t₂ Y₁ Y₂ mark u =
    signedPairOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark u := by
  have hx : (Real.sqrt (X₁*X₂):ℂ)⁻¹ =
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹ := by
    rw [Real.sqrt_mul hX₁,Complex.ofReal_mul,mul_inv_rev]
    ring
  have hy : (Real.sqrt (Y₁*Y₂):ℂ)⁻¹ =
      (Real.sqrt Y₁:ℂ)⁻¹*(Real.sqrt Y₂:ℂ)⁻¹ := by
    rw [Real.sqrt_mul hY₁,Complex.ofReal_mul,mul_inv_rev]
    ring
  rw [hprod] at hy
  unfold pairRowOn signedPairOn original
  rw [hx] at hy ⊢
  linear_combination
    (rowTwistedSum η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ Y₁ *
      rowTwistedSum η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ Y₂ * ∏ i∈T,mark i u)*hy

theorem actual_root_triangle {ι : Type} [Fintype ι] (T : Finset ι) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (mark : ι→FreeRow→ℂ) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) (hprod : Y₁*Y₂ = X₁*X₂) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      2*signedPairEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark +
      2*finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ Y₁ Y₂ mark := by
  have h := finite_uncentered_of_centered s
    (pairRowOn T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark)
    (pairRowOn T η₁ η₂ W₁ W₂ t₁ t₂ Y₁ Y₂ mark) (le_refl _) (le_refl _)
  simp_rw [pairRow_sub_eq_signed T η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark _
    hX₁ hX₂ hY₁ hY₂ hprod] at h
  rw [pairRow_energy,pairRow_energy] at h
  exact h

theorem reference_scales {U X₁ X₂ H : ℝ} (hU : 1 ≤ U) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hprod : X₁*X₂ ≤ U^((1+(23/20:ℝ))*(243/625))) (hH : (18023/25000:ℝ) ≤ H) :
    0 < U^shortWidth ∧ 0 < X₁*X₂/U^shortWidth ∧
      U^shortWidth*(X₁*X₂/U^shortWidth) = X₁*X₂ ∧
      X₁*X₂/U^shortWidth ≤ U^H := by
  have h := equal_product_reference (zero_lt_one.trans_le hU) hX₁ hX₂
  refine ⟨h.1,h.2.1,h.2.2,?_⟩
  exact (companion_length (zero_lt_one.trans_le hU) hprod).trans
    (Real.rpow_le_rpow_of_exponent_le hU hH)

/-- The root step only needs this exact product cap. The sharper paper
cap .83592 and companion .72092 are available in reference_scales. -/
theorem reference_scales_of_product {U X₁ X₂ H : ℝ} (hU : 0 < U)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hprod : X₁*X₂ ≤ U^(H+shortWidth)) :
    0 < U^shortWidth ∧ 0 < X₁*X₂/U^shortWidth ∧
      U^shortWidth*(X₁*X₂/U^shortWidth) = X₁*X₂ ∧
      X₁*X₂/U^shortWidth ≤ U^H := by
  have h := equal_product_reference hU hX₁ hX₂
  refine ⟨h.1,h.2.1,h.2.2,?_⟩
  apply (div_le_iff₀ h.1).mpr
  simpa only [Real.rpow_add hU] using hprod

#print axioms actual_root_triangle
#print axioms pairRow_sub_eq_signed
#print axioms reference_scales
end
end QRH.Cycle092.ReferenceShortP3
