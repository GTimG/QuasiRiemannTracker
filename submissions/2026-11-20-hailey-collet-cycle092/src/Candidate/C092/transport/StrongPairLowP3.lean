/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual finite P3 low branch for the independent pair. Both ordinary
columns, their masks/keeps and the original physical mark stay on one row set. -/
import Candidate.C092.transport.StrongPairLowSelected
import Candidate.C092.transport.LowActualP3

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- Literal rescaling of an earlier pair source to the actual retained
subproduct. Prime scales stay U^w and neither original ordinary is enlarged. -/
theorem retained_pair_at {N Y l bΦ mesh ε U V C : ℝ} {W : ℝ→ℂ}
    {η₁ η₂ η₀₁ η₀₂ : Character} {Q₁ Q₂ : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε (U^V)
      η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C)
    (F : Finset Slot) (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr)
    (w σ₁ σ₂ v₁ v₂ : Slot→ℝ) (t₁ t₂ height : ℝ)
    (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i/V ≤ mesh)
    (hσ₁lo : ∀ i,(33/50:ℝ) ≤ σ₁ i) (hσ₁hi : ∀ i,σ₁ i ≤ (33/50:ℝ))
    (hσ₂lo : ∀ i,(33/50:ℝ) ≤ σ₂ i) (hσ₂hi : ∀ i,σ₂ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv₁ : ∀ i,|v₁ i| ≤ height) (hv₂ : ∀ i,|v₂ i| ≤ height)
    (hwidth : (∑ i∈F,w i) ≤ V*l) (hU : 0 < U) (hV : 0 < V)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hXN : length (U^V) X₁ ≤ N) (hXY : length (U^V) X₂ ≤ Y)
    (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ)
    (hk₁ : ∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val)
    (hk₂ : ∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val)
    (hy : ∀ u∈s,rowNorm u ≤ U^V)
    (hmark₁ : ∀ u∈s,∀ i∈F,‖mark i u‖=
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖)
    (hmark₂ : ∀ u∈s,∀ i∈F,‖mark i u‖=
      ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖) :
    finiteEnergyOn F s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V*(1+ε)) := by
  have hwidth' : (∑ i∈F,w i/V) ≤ l := by
    rw [←Finset.sum_div]
    exact (div_le_iff₀ hV).2 (by simpa only [mul_comm] using hwidth)
  have h := hsrc F θ₁ θ₂ (fun i=>w i/V) σ₁ σ₂ v₁ v₂ t₁ t₂ height
    (fun i=>div_nonneg (hw i) hV.le) hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hwidth'
    p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy
    (by
      intro u hu i hi
      unfold QRH.Cycle092.WholeSlot.originalPools QRH.Cycle092.WholeSlot.originalCoefficients
      simp only [scale_rescale hU hV]
      exact hmark₁ u hu i hi)
    (by
      intro u hu i hi
      unfold QRH.Cycle092.WholeSlot.originalPools QRH.Cycle092.WholeSlot.originalCoefficients
      simp only [scale_rescale hU hV]
      exact hmark₂ u hu i hi)
  rw [←Real.rpow_mul hU.le] at h
  exact h

/-- The analytic P3 estimate after the actual complement response, source
error and slot buffer have been paid. This is a finite sum of the authentic
independent ordinary pair, not a scalar recurrence premise. -/
theorem low_pair_paid {N Y l bΦ mesh ε U V C e Cslot buffer L rounding allowance : ℝ}
    {W : ℝ→ℂ} {η₁ η₂ η₀₁ η₀₂ : Character} {Q₁ Q₂ : Ideal O}
    {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε (U^V)
      η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C)
    (F : Finset Slot) (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr)
    (w σ₁ σ₂ v₁ v₂ : Slot→ℝ) (t₁ t₂ height : ℝ)
    (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i/V ≤ mesh)
    (hσ₁lo : ∀ i,(33/50:ℝ) ≤ σ₁ i) (hσ₁hi : ∀ i,σ₁ i ≤ (33/50:ℝ))
    (hσ₂lo : ∀ i,(33/50:ℝ) ≤ σ₂ i) (hσ₂hi : ∀ i,σ₂ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv₁ : ∀ i,|v₁ i| ≤ height) (hv₂ : ∀ i,|v₂ i| ≤ height)
    (hretain : (∑ i∈F,w i) ≤ V*l) (hU : 1 ≤ U) (hV : 0 < V)
    (hC : 0 ≤ C) (hCslot : 0 ≤ Cslot) (he : 0 ≤ e)
    (hwidth : (∑ i,w i) ≤ L)
    (hdelete : (∑ i∈Finset.univ\F,w i) ≤ max 0 ((∑ i,w i)-V*l+rounding))
    (hprice : e*max 0 (L-V*l+rounding) < (u:ℝ)-(rho:ℝ)/2+allowance)
    (herr : buffer*((Finset.univ\F).card:ℝ)+V*ε ≤ (rho:ℝ)/4)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hXN : length (U^V) X₁ ≤ N) (hXY : length (U^V) X₂ ≤ Y)
    (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ)
    (hk₁ : ∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val)
    (hk₂ : ∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val)
    (hy : ∀ u∈s,rowNorm u ≤ U^V)
    (hmark₁ : ∀ u∈s,∀ i∈F,‖mark i u‖=
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr η₀₁ θ₁ W U w σ₁ v₁ i) t₁ (U^(w i))‖)
    (hmark₂ : ∀ u∈s,∀ i∈F,‖mark i u‖=
      ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr η₀₂ θ₂ W U w σ₂ v₂ i) t₂ (U^(w i))‖)
    (hlow : ∀ u∈s,∀ i∈Finset.univ\F,‖mark i u‖^2 ≤ (Cslot*U^buffer)*U^(e*w i)) :
    finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      Cslot^(Finset.univ\F).card*(C*QuadraticInitialBound.diagonalControl radialMajorant*
        (p.control controls)^2*(1+|t₁|+|t₂|+height)^degree)*U^(V+(u:ℝ)-(rho:ℝ)/4+allowance) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hE := retained_pair_at rayM Hr hHr hsrc F θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm
    hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hretain hUp hV p X₁ X₂ hX₁ hX₂ hXN hXY s mark
    hk₁ hk₂ hy hmark₁ hmark₂
  have hErase := finite_low_erasure Finset.univ F (Finset.subset_univ _) s η₁ η₂
    (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ U e (Cslot*U^buffer) w mark hUp hlow
  have hpay : 0 ≤ Cslot*U^buffer := by positivity
  have hpayment := p3_payment F w hU he hpay hwidth hdelete
  have hnonneg : 0 ≤ C*QuadraticInitialBound.diagonalControl radialMajorant*
      (p.control controls)^2*(1+|t₁|+|t₂|+height)^degree := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    positivity
  have hbound := (hErase.trans (mul_le_mul_of_nonneg_left hE (by positivity))).trans
    (mul_le_mul_of_nonneg_right hpayment (mul_nonneg hnonneg (Real.rpow_nonneg hUp.le _)))
  have hid := payment_with_buffer hUp Cslot buffer e (max 0 (L-V*l+rounding)) V ε (Finset.univ\F).card
  have hpaid : V+V*ε+buffer*((Finset.univ\F).card:ℝ)+e*max 0 (L-V*l+rounding) <
      V+(u:ℝ)-(rho:ℝ)/4+allowance := by linarith
  have hr := Real.rpow_le_rpow_of_exponent_le hU hpaid.le
  change finiteEnergyOn Finset.univ s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤ _
  calc
    _ ≤ ((Cslot*U^buffer)^(Finset.univ\F).card*U^(e*max 0 (L-V*l+rounding)))*
      ((C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree)*U^(V*(1+ε))) := hbound
    _ = (C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree)*
      (Cslot^(Finset.univ\F).card*U^(V+V*ε+buffer*((Finset.univ\F).card:ℝ)+e*max 0 (L-V*l+rounding))) := by
      rw [←hid]
      ring
    _ ≤ _ := by
      have hc : 0 ≤ (C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree)*Cslot^(Finset.univ\F).card := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hr hc]

#print axioms retained_pair_at
#print axioms low_pair_paid
end
end QRH.Cycle092.StrongPair
