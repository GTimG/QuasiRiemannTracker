/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual P3 energy after slot, source and whole-slot rounding fees. -/
import Candidate.C092.transport.LowActualBankUniform

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open QRH.Cycle092.NativeStrip QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle092.WholeSlot QRH.Cycle090 QRH.SourceCertificate
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open OAI.SevenEighths.Cycle61Moment CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM]
local instance c092LocalInst_Candidate_C092_transport_LowActualRadialEnergy_d14e2b98ad81a2c9_001 : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hr : Subgroup (O ⧸ rayM)ˣ) (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- This is the actual original marked low-row energy, with its original
ordinary factors, mask and keep, bounded after all three P3 fees. -/
theorem radial_low_energy {N Y l U V bslot a b bΦ mesh σlo σhi ε C e Cslot buffer L : ℝ}
    {W : ℝ → ℂ} {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : LabelledAt (α := Slot) rayM Hr hHr N Y l W bslot a b bΦ mesh
      σlo σhi 1 1 ε (U^V) η η₀ Q degree controls C)
    (F : Finset Slot) (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ)
    (t height rounding : ℝ) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i/V ≤ mesh)
    (hσlo : ∀ i, σlo ≤ σ i) (hσhi : ∀ i, σ i ≤ σhi)
    (hh : 0 ≤ height) (hv : ∀ i, |v i| ≤ height)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hU : 1 ≤ U) (hV : 0 < V) (hCslot : 0 ≤ Cslot)
    (hC : 0 ≤ C) (he : 0 ≤ e)
    (hbox : Box N Y (V*l) (length (U^V) X₁) (length (U^V) X₂) (∑ i ∈ F, w i))
    (hwidth : (∑ i, w i) ≤ L)
    (hdelete : (∑ i ∈ Finset.univ\F, w i) ≤ max 0 ((∑ i, w i)-V*l+rounding))
    (hprice : e*max 0 (L-V*l+rounding) < (u : ℝ)-(rho : ℝ)/2+(5/6)*max 0 ((H : ℝ)-V))
    (herr : buffer*((Finset.univ\F).card : ℝ)+V*ε ≤ (rho : ℝ)/4) :
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (originalPools rayM Hr bslot U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
      (fun i => U^(w i)) X₁ X₂
      (fun z => initialKeep η (internalQ Q η₀) z ∧
        LowRows Finset.univ η (fixedBadMask*idealGenerator 1) 1 t U e (Cslot*U^buffer) w
          (originalPools rayM Hr bslot U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
          (fun i => U^(w i)) z) Φ (U^V) ≤
      Cslot^(Finset.univ\F).card*
        (C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree)*U^(V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V)) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hpay : 0 ≤ Cslot*U^buffer := mul_nonneg hCslot (Real.rpow_pos_of_pos hUp _).le
  have hb := p3_actual_energy (e := e) rayM Hr hHr hsrc F θ w σ v t height hw hwm hσlo hσhi hh hv
    Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hUp hV hpay hbox
  have hnonneg : 0 ≤ C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
      (1+|t|+height)^degree := by
    have hdΦ := QuadraticInitialBound.diagonalControl_nonneg Φ
    positivity
  have hpm := p3_payment F w hU he hpay hwidth hdelete
  have hpm' := mul_le_mul_of_nonneg_right hpm
    (mul_nonneg hnonneg (Real.rpow_pos_of_pos hUp (V*(1+ε))).le)
  have hb' := hb.trans hpm'
  have hid := payment_with_buffer hUp Cslot buffer e (max 0 (L-V*l+rounding)) V ε (Finset.univ\F).card
  have hepaid : V+V*ε+buffer*((Finset.univ\F).card : ℝ)+e*max 0 (L-V*l+rounding) ≤
      V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V) := by linarith
  have hr := Real.rpow_le_rpow_of_exponent_le hU hepaid
  calc
    _ ≤ ((Cslot*U^buffer)^(Finset.univ\F).card*U^(e*max 0 (L-V*l+rounding)))*
        ((C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree)*U^(V*(1+ε))) := hb'
    _ = (C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree)*
        (Cslot^(Finset.univ\F).card*U^(V+V*ε+buffer*((Finset.univ\F).card : ℝ)+
          e*max 0 (L-V*l+rounding))) := by rw [←hid]; ring
    _ ≤ _ := by
      have hc : 0 ≤ (C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree)*Cslot^(Finset.univ\F).card := mul_nonneg hnonneg (pow_nonneg hCslot _)
      nlinarith [mul_le_mul_of_nonneg_left hr hc]

end
end QRH.Cycle092.LowActual
