/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual P3 energy after slot, source and whole-slot rounding fees. -/
import Candidate.C092.transport.LowActualSource

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

/-- Both genuine error exponents can be fixed positively after the finite
mark type, before all row data. The slot fee pays every possible erased slot. -/
theorem early_error_budget {d V : ℝ} (hd : 0 ≤ d) (hV : 0 ≤ V) (K : ℕ) :
    ∃ εslot εsrc : ℝ, 0 < εslot ∧ 0 < εsrc ∧
      2*εslot*d*(K : ℝ)+V*εsrc ≤ (rho : ℝ)/4 := by
  let E : ℝ := (rho : ℝ)/(16*(1+2*d*(K : ℝ)+V))
  have hk : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 1+2*d*(K : ℝ)+V := by positivity
  have hE : 0 < E := div_pos (by norm_num [rho]) (by positivity)
  refine ⟨E,E,hE,hE,?_⟩
  have hEq : E*(16*(1+2*d*(K : ℝ)+V)) = (rho : ℝ) := by
    dsimp [E]; field_simp
  nlinarith [mul_nonneg hd hk]

/-- With the exact scalar P3 price, spending the true slot count and the
retained-source error leaves a positive reserve in the native energy bound. -/
theorem paid_exponent {e width V sourceError buffer : ℝ} {k : ℕ}
    (hp : e*width < (u : ℝ)-(rho : ℝ)/2)
    (herr : buffer*(k : ℝ)+V*sourceError ≤ (rho : ℝ)/4) :
    V+V*sourceError+buffer*(k : ℝ)+e*width <
      V+(u : ℝ)-(rho : ℝ)/4 := by linarith

/-- At the induction radius H the actual P3 exponent saves 5u, including
its positive reserve; this is the source exponent before H.5 restoration. -/
theorem induction_exponent {n y e decrement mesh εslot εsrc d : ℝ} {k : ℕ}
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper : ℝ))
    (hd : 0 ≤ decrement) (hm : 0 ≤ mesh)
    (hround : 2*(responseUpper : ℝ)*((H : ℝ)*decrement+mesh) ≤ (rho : ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ))
    (herr : (2*εslot*d)*(k : ℝ)+(H : ℝ)*εsrc ≤ (rho : ℝ)/4) :
    (H : ℝ)+(H : ℝ)*εsrc+(2*εslot*d)*(k : ℝ)+
      e*max 0 (sourceWidth n y-(u : ℝ)-(H : ℝ)*
        (sourceWidth (n/(H : ℝ)) (y/(H : ℝ))-decrement)+mesh) <
      1-5*(u : ℝ)-(rho : ℝ)/4 := by
  have h := paid_exponent (p3_paid_with_rounding (n := n) he0 he1 hd hm hround hp) herr
  have hHu : (H : ℝ)+(u : ℝ) = 1-5*(u : ℝ) := by norm_num [H,u]
  linarith

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM]
local instance c092LocalInst_Candidate_C092_transport_LowActualP3_7ca9187b979217df_001 : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hr : Subgroup (O ⧸ rayM)ˣ) (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- This is the actual original marked low-row energy, with its original
ordinary factors, mask and keep, bounded after all three P3 fees. -/
theorem actual_low_energy {N Y l U V bslot a b bΦ mesh σlo σhi ε C e Cslot buffer L : ℝ}
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
    (hprice : e*max 0 (L-V*l+rounding) < (u : ℝ)-(rho : ℝ)/2)
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
          (1+|t|+height)^degree)*U^(V+(u : ℝ)-(rho : ℝ)/4) := by
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
  have hr := Real.rpow_le_rpow_of_exponent_le hU (paid_exponent hprice herr).le
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
