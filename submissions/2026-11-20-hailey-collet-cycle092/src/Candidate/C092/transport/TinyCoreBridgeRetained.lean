/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The original retained product from actual long and short fourth suppliers. -/
import Candidate.C092.transport.TinyCoreBridgeData

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open QRH.Cycle092.WholeSlot QRH.Cycle092.NativeStrip
local notation "O" => HeckeFamily.O

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- On the actual retained product, the long unmarked fourth and short
native duplicated-mark fourth recover exactly the original product seminorms. -/
theorem bridge_retained_energy {U V bΦ sourceMesh Cl Cs : ℝ} {W : ℝ → ℂ}
    {η η₀ : Character} {Q : Ideal O} {dl ds : ℕ} {Sl Ss : Finset (ℕ×ℕ)}
    (hsrc : LabelledAt (α := Fin 2×Slot) rayM Hr hHr bridgeCap bridgeCap bridgeWidth W
      2 (1/4) (9/4) bΦ sourceMesh (33/50) (33/50) 1 1 (1/10000) (U^V) η η₀ Q ds Ss Cs)
    (F : Finset Slot) (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot → ℝ)
    (t height : ℝ) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i/V ≤ sourceMesh)
    (hσlo : ∀ i, (33/50 : ℝ) ≤ σ i) (hσhi : ∀ i, σ i ≤ (33/50 : ℝ))
    (hh : 0 ≤ height) (hv : ∀ i, |v i| ≤ height)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hU : 1 < U) (hV : 0 < V) (hV1 : V ≤ 1)
    (hCl : 0 ≤ Cl) (hCs : 0 ≤ Cs)
    (hF : 2*(∑ i ∈ F, w i) ≤ V*bridgeWidth)
    (hshort : length (U^V) X₂ ≤ bridgeCap)
    (hlong : subsetEnergy (∅ : Finset Slot) η (fixedBadMask*idealGenerator 1) 1 t
      (p.profile 0) (p.profile 0) (originalPools rayM Hr 2 U w)
      (originalCoefficients rayM Hr hHr η₀ θ W U w σ v) (fun i => U^(w i)) X₁ X₁
      (initialKeep η (internalQ Q η₀)) Φ (U^V) ≤
      Cl*QuadraticInitialBound.diagonalControl Φ*((repeatedProfile p 0).control Sl)^2*
        (1+|t|+height)^dl*U^(V+1/10000)) :
    subsetEnergy F η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr η₀ θ W U w σ v)
      (fun i => U^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (U^V) ≤
      (Cl+Cs+1)*QuadraticInitialBound.diagonalControl Φ*(p.control (Sl∪Ss))^2*
        (1+|t|+height)^(max dl ds)*U^(V+1/1000) := by
  have hUp : 0 < U := zero_lt_one.trans hU
  have hUV : 1 < U^V := Real.one_lt_rpow hU hV
  have hbox : Box bridgeCap bridgeCap (V*bridgeWidth)
      (length (U^V) X₂) (length (U^V) X₂) (∑ j ∈ duplicated F, w j.2) := by
    refine ⟨length_nonneg _ _ hUV,length_nonneg _ _ hUV,Or.inl ⟨hshort,hshort⟩,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _ => hw j.2)
    · simpa [duplicated_sum] using hF
  have hshortE := labelled_retained_energy rayM Hr hHr hsrc (duplicated F)
    (fun j => θ j.2) (fun j => w j.2) (fun j => σ j.2) (fun j => v j.2) t height
    (fun j => hw j.2) (fun j => hwm j.2) (fun j => hσlo j.2) (fun j => hσhi j.2) hh (fun j => hv j.2)
    Φ hΦs hΦ (repeatedProfile p 1) X₂ X₂ hX₂ hX₂ hUp hV hbox
  have hcs := retained_energy_cauchy F η (fixedBadMask*idealGenerator 1) 1 t
    (p.profile 0) (p.profile 1) (originalPools rayM Hr 2 U w)
    (originalCoefficients rayM Hr hHr η₀ θ W U w σ v) (fun i => U^(w i)) X₁ X₂ (9/4) (9/4) hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2)
    (initialKeep η (internalQ Q η₀)) Φ (U^V) (Real.rpow_pos_of_pos hUp _) hΦ (fun i => (Real.rpow_pos_of_pos hUp _).le)
  let G := (Cl+Cs+1)*QuadraticInitialBound.diagonalControl Φ*(1+|t|+height)^(max dl ds)*U^(V+1/1000)
  let A := sourceControl (Sl∪Ss) (p.profile 0)
  let B := sourceControl (Sl∪Ss) (p.profile 1)
  have hheight : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hA0 := sourceControl_nonneg Sl (p.profile 0)
  have hB0 := sourceControl_nonneg Ss (p.profile 1)
  have hA := control_mono Sl (Sl∪Ss) Finset.subset_union_left (p.profile 0)
  have hB := control_mono Ss (Sl∪Ss) Finset.subset_union_right (p.profile 1)
  have hpowL := Real.rpow_le_rpow_of_exponent_le hU.le (show V+1/10000 ≤ V+1/1000 by norm_num)
  have hpowS := Real.rpow_le_rpow_of_exponent_le hU.le (show V*(1+(1/10000 : ℝ)) ≤ V+1/1000 by linarith only [hV1])
  have hL : subsetEnergy (∅ : Finset Slot) η (fixedBadMask*idealGenerator 1) 1 t
      (p.profile 0) (p.profile 0) (originalPools rayM Hr 2 U w)
      (originalCoefficients rayM Hr hHr η₀ θ W U w σ v) (fun i => U^(w i)) X₁ X₁
      (initialKeep η (internalQ Q η₀)) Φ (U^V) ≤ G*A^4 := by
    apply hlong.trans
    rw [repeated_control,←pow_mul]
    norm_num only [show (2 : ℕ)*2=4 from rfl]
    rw [show G*A^4 = (Cl+Cs+1)*QuadraticInitialBound.diagonalControl Φ*
      (sourceControl (Sl∪Ss) (p.profile 0))^4*(1+|t|+height)^(max dl ds)*U^(V+1/1000) by dsimp [G,A]; ring]
    have hCl' : Cl ≤ Cl+Cs+1 := by linarith
    have hd := pow_le_pow_right₀ hheight (le_max_left dl ds)
    gcongr
  have hS : subsetEnergy (duplicated F) η (fixedBadMask*idealGenerator 1) 1 t
      (p.profile 1) (p.profile 1) (fun j => originalPools rayM Hr 2 U w j.2)
      (fun j => originalCoefficients rayM Hr hHr η₀ θ W U w σ v j.2) (fun j => U^(w j.2)) X₂ X₂
      (initialKeep η (internalQ Q η₀)) Φ (U^V) ≤ G*B^4 := by
    apply hshortE.trans
    rw [repeated_control,←pow_mul]
    norm_num only [show (2 : ℕ)*2=4 from rfl]
    rw [show G*B^4 = (Cl+Cs+1)*QuadraticInitialBound.diagonalControl Φ*
      (sourceControl (Sl∪Ss) (p.profile 1))^4*(1+|t|+height)^(max dl ds)*U^(V+1/1000) by dsimp [G,B]; ring]
    have hCs' : Cs ≤ Cl+Cs+1 := by linarith
    have hd := pow_le_pow_right₀ hheight (le_max_right dl ds)
    gcongr
    · exact hU.le
    · linarith only [hV1]
  have h := hcs.trans (common_cauchy_factor hG hL hS)
  convert h using 1 <;> dsimp [G,A,B,Profiles.control] <;> ring

end
end QRH.Cycle092.TinyCore
