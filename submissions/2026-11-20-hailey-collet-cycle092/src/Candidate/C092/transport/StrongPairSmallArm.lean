/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual native suppliers for the two fourth arms of an independent pair. -/
import Candidate.C092.transport.StrongPairSmallNative
import Candidate.C092.transport.StrongPairSmallFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- A genuine native fourth at U^V with original U-based whole marks. -/
theorem small_native_arm {N q bΦ mesh ε U V C : ℝ} {W : ℝ→ℂ}
    {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : LabelledAt (α:=Fin 2×Slot) rayM Hr hHr N N (q/V) W
      2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε (U^V) η η₀ Q degree controls C)
    (F : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (t height : ℝ) (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i/V ≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ) ≤ σ i) (hσhi : ∀ i,σ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv : ∀ i,|v i| ≤ height)
    (hΦs : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (p : Profiles (1/4) (9/4)) (j : Fin 2) (X : ℝ) (hX : 0<X)
    (hU : 1<U) (hV : 0<V) (hXN : length (U^V) X ≤ N) (hquota : 2*(∑ i∈F,w i) ≤ q)
    (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ)
    (hk : ∀ u∈s,initialKeep η (internalQ Q η₀) u.val) (hy : ∀ u∈s,rowNorm u ≤ U^V)
    (hmark : ∀ u∈s,∀ i∈F,‖mark i u‖=
      ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr η₀ θ W U w σ v i) t (U^(w i))‖) :
    (∑ u∈s,(‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^2*
      ∏ i∈F,‖mark i u‖^2)^2) ≤
    C*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree*U^(V*(1+ε)) := by
  have hUp : 0<U:=zero_lt_one.trans hU
  have hUV : 1<U^V:=Real.one_lt_rpow hU hV
  have hbox : Box N N (V*(q/V)) (length (U^V) X) (length (U^V) X)
      (∑ k∈duplicated F,w k.2) := by
    refine ⟨length_nonneg _ _ hUV,length_nonneg _ _ hUV,Or.inl ⟨hXN,hXN⟩,
      Finset.sum_nonneg (fun i _=>hw i.2),?_⟩
    simpa only [duplicated_sum,mul_div_cancel₀ _ hV.ne'] using hquota
  have hE:=labelled_retained_energy rayM Hr hHr hsrc (duplicated F)
    (fun k=>θ k.2) (fun k=>w k.2) (fun k=>σ k.2) (fun k=>v k.2) t height
    (fun k=>hw k.2) (fun k=>hwm k.2) (fun k=>hσlo k.2) (fun k=>hσhi k.2)
    hh (fun k=>hv k.2) radialMajorant hΦs radialMajorant_nonneg (repeatedProfile p j)
    X X hX hX hUp hV hbox
  have hF:=finite_arm F s η (p.profile j) (originalPools rayM Hr 2 U w)
    (originalCoefficients rayM Hr hHr η₀ θ W U w σ v) (fun i=>U^(w i)) t X (9/4)
    (U^V) mark (fun _ hx=>(p.support j hx).2) hX
    (fun _=>Real.rpow_pos_of_pos hUp _) (Real.rpow_pos_of_pos hUp _)
    (initialKeep η (internalQ Q η₀)) hk hy hmark
  apply hF.trans
  rw [repeated_control,←pow_mul] at hE
  convert hE using 1
  rfl

#print axioms small_native_arm
end
end QRH.Cycle092.StrongPair
