/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootStep

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153RootStep
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands
open Cycle63FinalLow Cycle63InitialMass Cycle153RegionalLow Cycle153Reachable
open Cycle153Geometry
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Root cell slack is paid explicitly in the actual region gap. -/
theorem root_cell_gap_slack (w : α→ℝ) :
    @Cycle63.AffineLedger.regionGap Cycle153.Root.rootLedger (rootSourceCell w)-
      (rootSourceLength w+(6*Cycle153.FixedStages.stage0.price-1)*(∑i,w i)-
        Cycle153.FixedStages.stage0.intercept)=
    (6*Cycle153.FixedStages.stage0.price-Coordinates.outerLambda)*rootSourceSlack w := by
  change (Coordinates.outerB-Cycle153.FixedStages.stage0.intercept+
      (6*Cycle153.FixedStages.stage0.price-Coordinates.outerLambda)*rootSourceCell w)-_= _
  unfold rootSourceLength rootSourceSlack
  ring

/-- Literal source length at the chosen contracted root base. Original
remaining slot weights are not resampled or replaced by a model length. -/
theorem actual_root_child_length_rebase
    (s : Input α) (ch : Chain s) (χ : Character) (t Z : ℝ) (hZ : 1<Z)
    (n : ℕ) (bs Mrow omega xi reserve : ℝ) (w : α→ℝ)
    (g : LiveMainGeometry s ch Z Mrow (rootSourceAmp w) omega xi bs n)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2))) (Rdel : Finset α) :
    let r := nativeRootStepValues s ch χ t Z n bs Mrow omega xi reserve w g second L alloc Rdel
    let slots := ch.indices L alloc\Rdel
    0<r.u →
    (∑i : slots,w i)=r.childSlots ∧
    r.u*(length (Z^r.u) (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length (Z^r.u) (rawDaughterScale (ch.final χ t) second L alloc 1)+
      ∑i : slots,w i/r.u)=r.childA := by
  intro r slots hu
  have hs : (∑i : slots,w i)=∑i∈ch.indices L alloc\Rdel,w i := Finset.sum_coe_sort _ w
  refine ⟨hs,?_⟩
  have hx (X : ℝ) : r.u*length (Z^r.u) X=length Z X := by
    unfold length
    exact unit_mul_logb_rebase hZ hu
  rw [←Finset.sum_div,mul_add,mul_add,mul_div_cancel₀ _ (ne_of_gt hu),hx,hx,hs]
  rfl
end
end OAI.SevenEighths.Cycle153RootStep
#print axioms OAI.SevenEighths.Cycle153RootStep.root_cell_gap_slack
#print axioms OAI.SevenEighths.Cycle153RootStep.actual_root_child_length_rebase
