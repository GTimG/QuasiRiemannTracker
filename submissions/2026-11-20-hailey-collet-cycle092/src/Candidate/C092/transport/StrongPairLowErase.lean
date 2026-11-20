/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Positive whole-slot erasure on the SAME finite independent-character rows. -/
import Candidate.C092.transport.StrongPairCommon

set_option autoImplicit false
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

/-- The complement is charged only by the actual positive mark upper bound.
Both original ordinary factors, profiles, pitches and row set stay fixed. -/
theorem finite_mark_erasure {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T F : Finset Slot) (hFT : F ⊆ T) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) (cap : Slot→ℝ)
    (hmark : ∀ u∈s,∀ i∈T\F,‖mark i u‖^2 ≤ cap i) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      (∏ i∈T\F,cap i)*finiteEnergyOn F s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  unfold finiteEnergyOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hp := Finset.prod_le_prod₀ (fun i _=>sq_nonneg ‖mark i u‖) (fun i hi=>hmark u hu i hi)
  have he := Finset.prod_sdiff (f:=fun i=>‖mark i u‖^2) hFT
  rw [←he]
  have hh := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
      ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
      ∏ i∈F,‖mark i u‖^2 by positivity)
  convert hh using 1 <;> ring

/-- The true low-response fee on a retained whole subproduct. -/
theorem finite_low_erasure {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T F : Finset Slot) (hFT : F ⊆ T) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ U e pay : ℝ)
    (w : Slot→ℝ) (mark : Slot→FreeRow→ℂ) (hU : 0 < U)
    (hmark : ∀ u∈s,∀ i∈T\F,‖mark i u‖^2 ≤ pay*U^(e*w i)) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      (pay^(T\F).card*U^(e*∑ i∈T\F,w i))*
        finiteEnergyOn F s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  have h := finite_mark_erasure T F hFT s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark
    (fun i=>pay*U^(e*w i)) hmark
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hU,←Finset.mul_sum] using h

/-- Bounded whole marks are uniform on any actual original subproduct. -/
theorem finite_selected_bounded {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T F : Finset Slot) (hFT : F ⊆ T) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ)
    (mark : Slot→FreeRow→ℂ) (B : ℝ) (hB : 1 ≤ B)
    (hmark : ∀ u∈s,∀ i∈T\F,‖mark i u‖ ≤ B) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      B^(2*Fintype.card Slot)*finiteEnergyOn F s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark := by
  have h := finite_mark_erasure T F hFT s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark
    (fun _=>B^2) (fun u hu i hi=>pow_le_pow_left₀ (norm_nonneg _) (hmark u hu i hi) 2)
  have hcard : (T\F).card ≤ Fintype.card Slot := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (T\F))
  have hp : (∏ _i∈T\F,B^2) ≤ B^(2*Fintype.card Slot) := by
    rw [Finset.prod_const]
    have hB₂ : 1 ≤ B^2 := by nlinarith
    simpa only [←pow_mul] using pow_le_pow_right₀ hB₂ hcard
  exact h.trans (mul_le_mul_of_nonneg_right hp (by unfold finiteEnergyOn; positivity))

#print axioms finite_mark_erasure
#print axioms finite_low_erasure
end
end QRH.Cycle092.StrongPair
