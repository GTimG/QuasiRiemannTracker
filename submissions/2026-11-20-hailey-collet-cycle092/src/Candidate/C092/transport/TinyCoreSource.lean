/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Unconditional actual original energy at every radius 0<V<=.14. -/
import Candidate.C092.transport.TinyCoreSlots

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentCoreFloor CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O

/-- A genuine source for the complete original marked energy at tiny radii.
It covers all positive ordinary lengths and arbitrary original slot widths,
without a response class, a fourth-moment premise or a recursive source call.
The true character-modulus floor is absorbed after the fixed arithmetic data. -/
theorem original_tiny_source {n y : ℝ}
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn : y ≤ n)
    (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ → ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1 : ℝ) 2)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) (η η₀ : Character) (Q : Ideal O) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ, 0 ≤ V → V ≤ 7/50 →
    ∀ (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) → (∀ j, 0 ≤ σ j) → 0 ≤ height →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) → ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ → (∑ j, w j) ≤ sourceWidth n y-(u : ℝ) →
      energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
        (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
        (fun j => U^(w j)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (U^V) ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*
          U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) := by
  obtain ⟨B,hB,hcoeff⟩ := original_slot_coefficient_bound W hW hWs
  obtain ⟨degree,controls,Csrc,hCsrc,hfloorU⟩ := original_unmarked_floor
    (by norm_num : (0 : ℝ) < 1/10000) bΦ hbΦ η (internalQ Q η₀)
  let Cs : ℝ := ((256*B)^2)^(Fintype.card Slot)
  have hCs : 0 < Cs := pow_pos (pow_pos (mul_pos (by norm_num) hB) _) _
  refine ⟨degree,controls,Cs*Csrc,mul_pos hCs hCsrc,?_⟩
  filter_upwards [hfloorU,eventually_ge_atTop (1 : ℝ)] with U hfloorU hU
  intro V hV0 hV1 θ w σ v t height hw hσ hh Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hwidth
  have hUp : 0 < U := zero_lt_one.trans_le hU
  let r : CenteredMomentRadialEligibleEnergy.Radial := {
    keep := initialKeep η (internalQ Q η₀), profile := Φ, scale := U^V,
    scale_pos := Real.rpow_pos_of_pos hUp _, nonneg := fun _ => hΦ _ }
  have hP (j : Slot) : 0 < U^(w j) := Real.rpow_pos_of_pos hUp _
  have hcoef (j : Slot) (I : Ideal O) (_ : I ∈ originalPools rayM Hr 2 U w j) :
      ‖originalCoefficients rayM Hr hHr η₀ θ W U w σ v j I‖ ≤ B :=
    hcoeff _ _ _ _ _ (hP j) (hσ j)
  have hcap (j : Slot) (I : Ideal O) (_ : I ∈ originalPools rayM Hr 2 U w j)
      (hne : originalCoefficients rayM Hr hHr η₀ θ W U w σ v j I ≠ 0) :
      (I.absNorm : ℝ) ≤ 2*U^(w j) :=
    original_slot_norm_cap W hWs _ _ _ _ _ (hP j) hne
  have hsprod (z : O) (_ : r.keep z) :
      (∏ j, ‖CenteredMomentHeckeSlots.rowSlot η (fixedBadMask*idealGenerator 1) 1 z
        (originalPools rayM Hr 2 U w j) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v j) t‖^2/U^(w j)) ≤
      Cs*U^(∑ j, w j) := by
    have h := slot_product_absolute η (fixedBadMask*idealGenerator 1) 1 z t B hB.le
      (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
      (fun j => U^(w j)) hP hcoef hcap
    simpa [Cs,Real.rpow_sum_of_pos hUp] using h
  have hred := slot_energy_reduction η (fixedBadMask*idealGenerator 1) 1 t
    (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) hX₁ hX₂
    (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
    (fun j => U^(w j)) hP r (Cs*U^(∑ j, w j)) hsprod
  have hfloor := hfloorU hU V hV0 Φ hΦs hΦ p t height X₁ X₂ hh hX₁ hX₂
  have hS : 0 ≤ ∑ j, w j := Finset.sum_nonneg (fun j _ => hw j)
  have hSmax := hwidth.trans (original_width_cap hy0 hy1 hn)
  have hpaid := tiny_floor_paid (K := 0) hV0 hV1 (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 1) hS hSmax (by norm_num : (0 : ℝ)*(0 : ℕ) ≤ 1/1000)
  simp only [Nat.cast_zero,mul_zero,add_zero,one_mul] at hpaid
  have hmono := Real.rpow_le_rpow_of_exponent_le hU hpaid
  have hdΦ := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hfac : 0 ≤ (Cs*Csrc)*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmono hfac
  calc
    _ ≤ (Cs*U^(∑ j, w j))*
        (Csrc*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree*U^(5*V+5*(1/10000 : ℝ))) :=
      hred.trans (mul_le_mul_of_nonneg_left hfloor (by positivity))
    _ = ((Cs*Csrc)*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree)*
        U^(5*V+5*(1/10000 : ℝ)+(∑ j, w j)) := by rw [Real.rpow_add hUp (5*V+5*(1/10000 : ℝ)) (∑ j, w j)]; ring
    _ ≤ _ := hmul

end
end QRH.Cycle092.TinyCore
