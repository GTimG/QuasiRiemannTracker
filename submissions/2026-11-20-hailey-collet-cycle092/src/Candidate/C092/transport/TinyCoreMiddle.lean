/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Original marked low-response energy through V=7/8, using genuine unmarked input. -/
import Candidate.C092.transport.TinyCoreErasure

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentCoreFloor CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge CenteredMomentEnergyBands
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.NativeStrip QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O

/-- No ordinary factor is required to lie below half the radius. The genuine
incumbent unmarked source is invoked at the original base U and original row
state; all marks are erased only on their actual positive low-response class. -/
theorem original_middle_source {n y e : ℝ}
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ 3/4)
    (Slot : Type) [Fintype Slot] [DecidableEq Slot] :
    ∃ buffer : ℝ, 0 < buffer ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
      (W : ℝ → ℂ) (bΦ : ℝ), 0 < bΦ →
    ∀ (η η₀ : Character) (Q : Ideal O), Q ≤ rayM →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∀ Cslot : ℝ, 0 ≤ Cslot →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop,
    ∀ V : ℝ, 0 ≤ V → V ≤ 7/8 →
    ∀ (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ) (t height : ℝ),
      (∀ j, 0 ≤ w j) → 0 ≤ height →
    ∀ (Φ : 𝓢(ℝ,ℂ)), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
      (∀ x, 0 ≤ (Φ x).re) → ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),
      0 < X₁ → 0 < X₂ → Box n y 0 (length U X₁) (length U X₂) 0 →
      (∑ j, w j) ≤ sourceWidth n y-(u : ℝ) →
      energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
        (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
        (fun j => U^(w j)) X₁ X₂
        (fun z => initialKeep η (internalQ Q η₀) z ∧
          LowRows Finset.univ η (fixedBadMask*idealGenerator 1) 1 t U e (Cslot*U^buffer) w
            (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
            (fun j => U^(w j)) z) Φ (U^V) ≤
        C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree*
          U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) := by
  let buffer : ℝ := 1/(10000*(1+(Fintype.card Slot : ℝ)))
  have hb : 0 < buffer := by dsimp [buffer]; positivity
  have hbfee : buffer*(Fintype.card Slot : ℝ) ≤ 1/10000 := by
    have heq : buffer*(10000*(1+(Fintype.card Slot : ℝ))) = 1 := by dsimp [buffer]; field_simp
    nlinarith only [heq,hb]
  refine ⟨buffer,hb,?_⟩
  intro rayM _ Hr hHr W bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72 Cslot hCslot
  obtain ⟨degree,controls,Csrc,hCsrc,hfloorU⟩ := original_unmarked_source hβ rayM Hr hHr bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  let Cs := (max 1 Cslot)^(Fintype.card Slot)
  have hCs : 0 < Cs := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨degree,controls,Cs*Csrc,mul_pos hCs hCsrc,?_⟩
  filter_upwards [hfloorU,eventually_gt_atTop (1 : ℝ)] with U hfloorU hU
  intro V hV0 hV1 θ w σ v t height hw hh Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox hwidth
  have hUp : 0 < U := zero_lt_one.trans hU
  let r : CenteredMomentRadialEligibleEnergy.Radial := {
    keep := initialKeep η (internalQ Q η₀), profile := Φ, scale := U^V,
    scale_pos := Real.rpow_pos_of_pos hUp _, nonneg := fun _ => hΦ _ }
  have hP (j : Slot) : 0 ≤ U^(w j) := (Real.rpow_pos_of_pos hUp _).le
  have hpay : 0 ≤ Cslot*U^buffer := mul_nonneg hCslot (Real.rpow_pos_of_pos hUp _).le
  have hred := erase_all_low_energy η (fixedBadMask*idealGenerator 1) 1 t U e (Cslot*U^buffer) w
    (p.profile 0) (p.profile 1) (originalPools rayM Hr 2 U w)
    (originalCoefficients rayM Hr hHr η₀ θ W U w σ v) (fun j => U^(w j)) X₁ X₂ (9/4) (9/4) r hΦ
    hX₁ hX₂ (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) hUp hpay hP
  have hn1' : n ≤ 1 := by norm_num [sourceRatio,sourceY] at hn1 hy1; linarith only [hn1,hy1]
  have hy1' : y ≤ 1 := hy1.trans (by norm_num [sourceY])
  obtain ⟨hX₁U,hX₂U⟩ := ordinary_lengths_below_U hU hn1' hy1' hbox
  have hfloor := hfloorU hU.le V hV0 (hV1.trans (by norm_num)) Φ hΦs hΦ p t height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U
  have hS : 0 ≤ ∑ j, w j := Finset.sum_nonneg (fun j _ => hw j)
  have hSmax := hwidth.trans (original_width_cap_sharp hy0 hy1 hn0)
  have hpaid := unmarked_middle_paid hV1 he1 hS hSmax hbfee
  have hmono := Real.rpow_le_rpow_of_exponent_le hU.le hpaid
  have hdΦ := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hfac : 0 ≤ (Cs*Csrc)*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree := by positivity
  have hcpow : Cslot^(Fintype.card Slot) ≤ Cs := by dsimp [Cs]; gcongr; exact le_max_right _ _
  calc
    _ ≤ ((Cslot*U^buffer)^(Fintype.card Slot)*U^(e*∑ j, w j))*
        (Csrc*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree*U^(V+1/10000)) :=
      hred.trans (mul_le_mul_of_nonneg_left hfloor (by positivity))
    _ = (Cslot^(Fintype.card Slot)*Csrc*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree)*
        U^(V+1/10000+buffer*(Fintype.card Slot : ℝ)+e*∑ j, w j) := by
      rw [mul_pow,←Real.rpow_mul_natCast hUp.le]
      rw [Real.rpow_add hUp (V+1/10000+buffer*(Fintype.card Slot : ℝ)) (e*∑ j,w j),
        Real.rpow_add hUp (V+1/10000) (buffer*(Fintype.card Slot : ℝ))]
      ring
    _ ≤ _ := by
      have hpctrl := p.control_nonneg controls
      gcongr

end
end QRH.Cycle092.TinyCore
