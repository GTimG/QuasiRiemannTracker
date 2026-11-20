/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual native suppliers for the two fourth arms of an independent pair. -/
import Candidate.C092.transport.StrongPairFinite

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

/-- A genuine source specialization, with every selected mark duplicated.
The finite original keep, radial ball, character and normalized kernel are
exactly those of the established native supplier. -/
theorem native_arm {N quota bΦ mesh ε Z C : ℝ} {W : ℝ→ℂ}
    {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : LabelledAt (α:=Fin 2×Slot) rayM Hr hHr N N quota W
      2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C)
    (F : Finset Slot) (θ : Slot → RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (t height : ℝ) (hw : ∀ i,0≤w i) (hwm : ∀ i,w i≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ)≤σ i) (hσhi : ∀ i,σ i≤(33/50:ℝ))
    (hh : 0≤height) (hv : ∀ i,|v i|≤height)
    (hΦs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (p : Profiles (1/4) (9/4)) (j : Fin 2) (X : ℝ) (hX : 0<X)
    (hZ : 1<Z) (hXN : length Z X≤N) (hquota : 2*(∑ i∈F,w i)≤quota)
    (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ)
    (hk : ∀ u∈s,initialKeep η (internalQ Q η₀) u.val) (hy : ∀ u∈s,rowNorm u≤Z)
    (hmark : ∀ u∈s,∀ i∈F,‖mark i u‖=
      ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀ θ W Z w σ v i) t (Z^(w i))‖) :
    (∑ u∈s,(‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^2*
      ∏ i∈F,‖mark i u‖^2)^2) ≤
    C*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree*Z^(1+ε) := by
  have hbox : Box N N (1*quota) (length (Z^(1:ℝ)) X) (length (Z^(1:ℝ)) X)
      (∑ k∈duplicated F,w k.2) := by
    simp only [Real.rpow_one,one_mul]
    exact ⟨length_nonneg _ _ hZ,length_nonneg _ _ hZ,Or.inl ⟨hXN,hXN⟩,
      Finset.sum_nonneg (fun i _=>hw i.2),by simpa only [duplicated_sum] using hquota⟩
  have hsrc' : LabelledAt (α:=Fin 2×Slot) rayM Hr hHr N N quota W
      2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε (Z^(1:ℝ)) η η₀ Q degree controls C := by
    simpa only [Real.rpow_one] using hsrc
  have hE := labelled_retained_energy rayM Hr hHr hsrc' (duplicated F)
    (fun k=>θ k.2) (fun k=>w k.2) (fun k=>σ k.2) (fun k=>v k.2) t height
    (fun k=>hw k.2) (fun k=>by simpa only [div_one] using hwm k.2)
    (fun k=>hσlo k.2) (fun k=>hσhi k.2) hh (fun k=>hv k.2)
    radialMajorant hΦs radialMajorant_nonneg (repeatedProfile p j) X X hX hX
    (zero_lt_one.trans hZ) one_pos hbox
  have hF := finite_arm F s η (p.profile j)
    (originalPools rayM Hr 2 Z w) (originalCoefficients rayM Hr hHr η₀ θ W Z w σ v)
    (fun i=>Z^(w i)) t X (9/4) Z mark (fun _ hx=>(p.support j hx).2) hX
    (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (zero_lt_one.trans hZ)
    (initialKeep η (internalQ Q η₀)) hk hy hmark
  apply hF.trans
  rw [repeated_control,←pow_mul] at hE
  convert hE using 1 <;> simp only [Real.rpow_one,one_mul,repeatedProfile,show (2:ℕ)*2=4 from rfl]
  rfl

#print axioms native_arm
end
end QRH.Cycle092.StrongPair
