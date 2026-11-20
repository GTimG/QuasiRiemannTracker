/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite authentic two-anchor energies. A common physical mark is represented
at each anchor by an exact norm equality, not by a new analytic bound. -/
import Candidate.C092.transport.StrongPairSmallUnmarked

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

/-- Exact deletion on the same finite rows and physical marks. -/
theorem finite_delete_on {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T F : Finset Slot) (hFT : F ⊆ T) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) (pay U e : ℝ) (w : Slot→ℝ)
    (hU : 0<U) (hpay : 0≤pay)
    (hlow : ∀ u∈s,∀ i∈T\F,‖mark i u‖^2≤pay*U^(e*w i)) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      (pay^(T\F).card*U^(e*∑ i∈T\F,w i))*
        finiteEnergyOn F s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  rw [finiteEnergyOn,finiteEnergyOn,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hp := Finset.prod_le_prod₀ (s:=T\F) (f:=fun i=>‖mark i u‖^2)
    (g:=fun i=>pay*U^(e*w i)) (fun i _=>sq_nonneg _) (fun i hi=>hlow u hu i hi)
  have he : (∏ i∈T\F,pay*U^(e*w i))=pay^(T\F).card*U^(e*∑ i∈T\F,w i) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hU]
    congr 1
    rw [Finset.mul_sum]
  rw [he] at hp
  have ht := Finset.prod_sdiff (f:=fun i=>‖mark i u‖^2) hFT
  have hp0 : 0≤∏ i∈F,‖mark i u‖^2 := Finset.prod_nonneg (fun i _=>sq_nonneg _)
  calc
    _ = (∏ i∈T\F,‖mark i u‖^2)*
      (‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
       ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
       ∏ i∈F,‖mark i u‖^2) := by rw [←ht]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)

/-- No analytic hypothesis is hidden in this erasure; F is literally empty. -/
theorem finite_delete_all {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) (pay U e : ℝ) (w : Slot→ℝ)
    (hU : 0<U) (hpay : 0≤pay)
    (hlow : ∀ u∈s,∀ i∈T,‖mark i u‖^2≤pay*U^(e*w i)) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      (pay^T.card*U^(e*∑ i∈T,w i))*
        (∑ u∈s,‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
          ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2) := by
  simpa only [Finset.sdiff_empty,finiteEnergyOn,Finset.prod_empty,mul_one] using
    finite_delete_on T ∅ (Finset.empty_subset _) s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂
      mark pay U e w hU hpay (by simpa only [Finset.sdiff_empty] using hlow)

#print axioms finite_delete_on
end
end QRH.Cycle092.StrongPair
