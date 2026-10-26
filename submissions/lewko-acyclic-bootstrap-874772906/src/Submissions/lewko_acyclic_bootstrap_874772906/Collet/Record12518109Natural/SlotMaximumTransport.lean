/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Uses the exact OpenAI/math natural masked coefficient identity and Cycle61
common allocation interfaces, Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.WeightedHighRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondSourceControls
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Record12518109Natural.WeightedHigh
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAmplificationChildInput
open CenteredMomentCommonProfile CenteredMomentEligibleEnergy
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

/-- Exact physical normalized slot, including its common height and puncture. -/
theorem masked_natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (P t : ℝ) :
    normalizedSlot η (fixedBadMask*idealGenerator R) 1 z pool β t P =
      naturalSlot (excluded F.character R) pool (heightCoefficient β t) P := by
  unfold normalizedSlot naturalSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR]
  simp only [heightCoefficient,one_mul]
  ring

private theorem subtype_prod_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι→ℝ) (hf : ∀i,1≤f i) :
    (∏i : S,f i) ≤ ∏i,f i := by
  rw [Finset.prod_coe_sort S f]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (hf i)) (fun i _ _=>hf i)

/-- Common allocation changes only the live index set in the slot factor.
Its actual new row character, mask and height stay inside every slot. -/
theorem common_source_maximum_le_original {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (E R : Ideal O) (pick : actualAllocations s.pools E)
    (τ : Character) (t : ℝ) (z : O) :
    sourceSlotMaximum (commonData (withHeight s τ t) E R pick) z ≤
      ∏k, max 1 (‖normalizedSlot τ (fixedBadMask*idealGenerator (R*E)) 1 z
        (s.slots k) (s.coefficient k) t (s.P k)‖^2) := by
  exact subtype_prod_le (liveIndices pick.val) (fun k : ι=>
    max 1 (‖normalizedSlot τ (fixedBadMask*idealGenerator (R*E)) 1 z
      (s.slots k) (s.coefficient k) t (s.P k)‖^2)) (fun _=>le_max_left _ _)

/-- Both common allocations may delete slots; the maximum product over the
fixed original family majorizes them without a marked-width loss. -/
theorem two_common_source_maximum_le_original {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (χ₁ : Character) (t₁ : ℝ) (E R₂ : Ideal O)
    (pick : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools E)
    (τ : Character) (t : ℝ) (z : O) :
    sourceSlotMaximum (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) τ t) E R₂ pick) z ≤
      ∏k, max 1 (‖normalizedSlot τ (fixedBadMask*idealGenerator (R₂*E)) 1 z
        (s.slots k) (s.coefficient k) t (s.P k)‖^2) := by
  apply (common_source_maximum_le_original (child s C₁ R₁ B₁ χ₁ t₁) E R₂ pick τ t z).trans
  exact subtype_prod_le (liveIndices B₁.val) (fun k : ι=>
    max 1 (‖normalizedSlot τ (fixedBadMask*idealGenerator (R₂*E)) 1 z
      (s.slots k) (s.coefficient k) t (s.P k)‖^2)) (fun _=>le_max_left _ _)

/-- The enlarged physical product is exactly the natural-row product needed
by the root/max supplier. All original marked slots and heights remain. -/
theorem two_common_source_maximum_le_natural {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (χ₁ : Character) (t₁ : ℝ) (E R₂ : Ideal O)
    (pick : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools E)
    (τ : Character) (t : ℝ) (z : O) (F : NaturalRow τ z) (hR : R₂*E≠0) :
    sourceSlotMaximum (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) τ t) E R₂ pick) z ≤
      ∏k, max 1 (‖naturalSlot (excluded F.character (R₂*E)) (s.slots k)
        (heightCoefficient (s.coefficient k) t) (s.P k)‖^2) := by
  apply (two_common_source_maximum_le_original s C₁ R₁ B₁ χ₁ t₁ E R₂ pick τ t z).trans_eq
  exact Finset.prod_congr rfl (fun k _=>by rw [masked_natural_slot_eq F _ hR])

end
end OAI.SevenEighths.Record12518109Natural.WeightedHigh
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.masked_natural_slot_eq
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.common_source_maximum_le_original
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.two_common_source_maximum_le_original
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.two_common_source_maximum_le_natural
