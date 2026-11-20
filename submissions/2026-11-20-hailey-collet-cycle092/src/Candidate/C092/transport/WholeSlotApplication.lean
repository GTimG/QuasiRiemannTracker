/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   P3 on the original positive energy, with whole labelled slots retained. -/
import Candidate.C092.transport.WholeSlotSelection

set_option autoImplicit false
namespace QRH.Cycle092.WholeSlot
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open QRH.Cycle092.NativeStrip QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open OAI.SevenEighths.Cycle61Moment CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

/-- Original slot scales are identical after the source is based at U^V. -/
theorem scale_rescale {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (w : ℝ) :
    (U^V)^(w/V) = U^w := by
  rw [←Real.rpow_mul hU.le]
  congr 1
  field_simp

/-- One common early mesh works at every radius above its fixed lower bound. -/
theorem mesh_rescale {mesh sourceMesh Vmin V w : ℝ}
    (hVmin : 0 < Vmin) (hV : Vmin ≤ V) (hs : 0 ≤ sourceMesh)
    (hm : mesh ≤ Vmin*sourceMesh) (hw : w ≤ mesh) : w/V ≤ sourceMesh := by
  apply (div_le_iff₀ (hVmin.trans_le hV)).2
  have h := mul_le_mul_of_nonneg_right hV hs
  nlinarith

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM]
local instance c092LocalInst_Candidate_C092_transport_WholeSlotApplication_da21df30f02cf312_001 : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hr : Subgroup (O ⧸ rayM)ˣ) (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

def originalPools (bslot U : ℝ) (w : Slot → ℝ) : Slot → Finset (Ideal O) :=
  fun i => primePool rayM Hr bslot (U^(w i))

def originalCoefficients (η₀ : Character) (θ : Slot → RayQuotient.Characters rayM Hr)
    (W : ℝ → ℂ) (U : ℝ) (w σ v : Slot → ℝ) : Slot → Ideal O → ℂ :=
  fun i I => idealCoeff (relativeCharacter rayM Hr hHr η₀ (θ i)) I *
    HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (v i) I

/-- The earlier labelled source applies to the exact retained pools, character
coefficients, phases and profiles at U^V, using relative widths w/V. -/
theorem labelled_retained_energy {N Y l U V bslot a b bΦ mesh σlo σhi ε C : ℝ}
    {W : ℝ → ℂ} {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : LabelledAt (α := Slot) rayM Hr hHr N Y l W bslot a b bΦ mesh
      σlo σhi 1 1 ε (U^V) η η₀ Q degree controls C)
    (F : Finset Slot) (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ)
    (t height : ℝ) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i/V ≤ mesh)
    (hσlo : ∀ i, σlo ≤ σ i) (hσhi : ∀ i, σ i ≤ σhi)
    (hh : 0 ≤ height) (hv : ∀ i, |v i| ≤ height)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hU : 0 < U) (hV : 0 < V)
    (hbox : Box N Y (V*l) (length (U^V) X₁) (length (U^V) X₂) (∑ i ∈ F, w i)) :
    subsetEnergy F η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (originalPools rayM Hr bslot U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
      (fun i => U^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (U^V) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
        (1+|t|+height)^degree*U^(V*(1+ε)) := by
  obtain ⟨hx,hz,hpair,hs₀,hs₁⟩ := hbox
  have hsum : (∑ i : F, w i.val/V) = (∑ i ∈ F, w i)/V := by
    rw [←Finset.sum_div,Finset.sum_coe_sort]
  have hbox' : Box N Y l (length (U^V) X₁) (length (U^V) X₂) (∑ i : F, w i.val/V) := by
    refine ⟨hx,hz,hpair,?_,?_⟩
    · rw [hsum]; exact div_nonneg hs₀ hV.le
    · rw [hsum]
      apply (div_le_iff₀ hV).2
      nlinarith
  have h := hsrc F (fun i => θ i.val) (fun i => w i.val/V) (fun i => σ i.val)
    (fun i => v i.val) t height (fun i => div_nonneg (hw i.val) hV.le)
    (fun i => hwm i.val) (fun i => hσlo i.val) (fun i => hσhi i.val) hh (fun i => hv i.val)
    1 le_rfl le_rfl Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox'
  simp_rw [scale_rescale hU hV] at h
  simp only [Real.rpow_one] at h
  rw [←Real.rpow_mul hU.le] at h
  exact h

/-- Genuine P3 application: the actual full marked low-row energy is bounded
by the earlier retained source, with the exact whole-slot erasure payment.
The same keep, mask, original ordinary factors and all retained slots survive. -/
theorem p3_actual_energy {N Y l U V bslot a b bΦ mesh σlo σhi ε C e pay : ℝ}
    {W : ℝ → ℂ} {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : LabelledAt (α := Slot) rayM Hr hHr N Y l W bslot a b bΦ mesh
      σlo σhi 1 1 ε (U^V) η η₀ Q degree controls C)
    (F : Finset Slot) (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ)
    (t height : ℝ) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i/V ≤ mesh)
    (hσlo : ∀ i, σlo ≤ σ i) (hσhi : ∀ i, σ i ≤ σhi)
    (hh : 0 ≤ height) (hv : ∀ i, |v i| ≤ height)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hU : 0 < U) (hV : 0 < V) (hpay : 0 ≤ pay)
    (hbox : Box N Y (V*l) (length (U^V) X₁) (length (U^V) X₂) (∑ i ∈ F, w i)) :
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (originalPools rayM Hr bslot U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
      (fun i => U^(w i)) X₁ X₂
      (fun z => initialKeep η (internalQ Q η₀) z ∧
        LowRows Finset.univ η (fixedBadMask*idealGenerator 1) 1 t U e pay w
          (originalPools rayM Hr bslot U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
          (fun i => U^(w i)) z) Φ (U^V) ≤
      (pay^(Finset.univ\F).card*U^(e*∑ i ∈ Finset.univ\F, w i))*
        (C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
          (1+|t|+height)^degree*U^(V*(1+ε))) := by
  have hP : ∀ i, 0 ≤ U^(w i) := fun i => (Real.rpow_pos_of_pos hU _).le
  have hleft := low_energy_erasure Finset.univ F (Finset.subset_univ _)
    η (fixedBadMask*idealGenerator 1) 1 t U e pay w (p.profile 0) (p.profile 1)
    (originalPools rayM Hr bslot U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
    (fun i => U^(w i)) X₁ X₂ b b hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2)
    (initialKeep η (internalQ Q η₀)) Φ hΦ (U^V) (Real.rpow_pos_of_pos hU _) hU hpay hP
  rw [subsetEnergy_univ] at hleft
  · exact hleft.trans (mul_le_mul_of_nonneg_left
      (labelled_retained_energy rayM Hr hHr hsrc F θ w σ v t height hw hwm hσlo hσhi hh hv
        Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hU hV hbox) (by positivity))
  · exact (mul_pos hX₁ hX₂).le
  · exact hP

/-- The paid P3 positive part follows from the actual erased whole widths.
When no slot needs erasing the exact payment is one, with zero exponent. -/
theorem p3_payment {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (F : Finset Slot) (w : Slot → ℝ) {U e pay L V l mesh : ℝ}
    (hU : 1 ≤ U) (he : 0 ≤ e) (hpay : 0 ≤ pay)
    (hwidth : (∑ i, w i) ≤ L)
    (hdelete : (∑ i ∈ Finset.univ\F, w i) ≤ max 0 ((∑ i, w i)-V*l+mesh)) :
    pay^(Finset.univ\F).card*U^(e*∑ i ∈ Finset.univ\F, w i) ≤
      pay^(Finset.univ\F).card*U^(e*max 0 (L-V*l+mesh)) := by
  have hmax := max_le_max_left 0 (show (∑ i, w i)-V*l+mesh ≤ L-V*l+mesh by linarith)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU
    (mul_le_mul_of_nonneg_left (hdelete.trans hmax) he)) (pow_nonneg hpay _)

@[simp] theorem exhausted_payment {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (w : Slot → ℝ) (U e pay : ℝ) :
    pay^(Finset.univ\(Finset.univ : Finset Slot)).card*
      U^(e*∑ i ∈ Finset.univ\(Finset.univ : Finset Slot), w i) = 1 := by simp

end
end QRH.Cycle092.WholeSlot
