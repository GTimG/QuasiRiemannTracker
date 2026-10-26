/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalChildGeometry
import Candidate.Research.RecursiveAffine.NativePhysicalCoordinates
import Candidate.Research.RecursiveAffine.PhysicalMaskBridge
import Candidate.Research.RecursiveAffine.RoundedDeletion

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentEnergyBands Cycle153Geometry Cycle153ReachableGeometry Cycle63.Optimization

/-- The actual original slot sum picks the sole cell of a regional
ledger. No arbitrary cell is substituted for the source-selected one. -/
theorem regional_actual_cell {S : Cycle153.RegionalStage} {P : Cycle153.RegionalPosition}
    (hP : P.Facts S) {z : ℝ} (hz : P.slotTop-P.mesh ≤ z ∧ z ≤ P.slotTop) :
    @Cycle63.AffineLedger.cellUpper (Cycle153.regionalLedger S P hP)
      (@Cycle63.AffineLedger.originalCell (Cycle153.regionalLedger S P hP) z)=P.slotTop := by
  have hm := @Cycle63.AffineLedger.originalCell_mem (Cycle153.regionalLedger S P hP) z hz
  have hcell : @Cycle63.AffineLedger.originalCell (Cycle153.regionalLedger S P hP) z=1 :=
    le_antisymm hm.2.1 hm.1
  rw [hcell]
  change P.slotTop-P.mesh+((1:ℕ):ℝ)*P.mesh=P.slotTop
  push_cast
  ring

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)

/-- The unrounded local amplifier is the literal normalized global model. -/
theorem node_model_amplifier_identity :
    modelAmplification j N.coordinates/N.unit=
      planeAmplifier (innerStage j.val).price (innerStage j.val).intercept
        (innerStage j.val).q (innerStage j.val).lam N.plane
        (∑i : N.slots,C.originalWeight i/N.unit) := by
  have hslots : (∑i : N.slots,C.originalWeight i/N.unit)=modelSlots j N.coordinates/N.unit := by
    rw [←Finset.sum_div,N.slots_eq]
  have hplane : rawPlane j N.coordinates=modelPlane j N.coordinates := by
    fin_cases j <;> rfl
  rw [N.plane_eq,hslots,modelAmplification_identity,hplane]
  unfold planeAmplifier
  rw [←N.unit_eq]
  field_simp [ne_of_gt N.unit_pos]
  <;> ring

/-- The actual native amplifier is the one computed from this retained
source's rounded plane and original slots. Its displacement from the
fixed global model is bounded and nonnegative. -/
theorem actual_node_amp_bounds :
    letI : Cycle63.AffineLedger := N.ledger
    let actualAmp := Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))
    modelAmplification j N.coordinates/N.unit ≤ actualAmp ∧
      actualAmp ≤ modelAmplification j N.coordinates/N.unit+42*(1/C.gridDenominator) := by
  letI : Cycle63.AffineLedger := N.ledger
  intro actualAmp
  have hcell := regional_actual_cell N.positionFacts ⟨N.window.slots_ge,N.window.slots_le⟩
  have ha : actualAmp=(innerStage j.val).amp N.position := by
    dsimp only [actualAmp]
    rw [hcell]
    rfl
  have hround := Cycle153.rounded_amplifier_bounds (innerStage j.val)
    (g:=1/C.gridDenominator)
    (B:=N.plane) (z:=∑i : N.slots,C.originalWeight i/N.unit)
    (n₁:=length N.localBase N.X1) (n₂:=length N.localBase N.X2)
    (by
      have hn : (0:ℝ)<C.gridDenominator := by exact_mod_cast C.grid_positive
      positivity)
    (inner_stage_ratio j)
  rw [←N.rounded,←ha] at hround
  have hmodel := node_model_amplifier_identity N
  rw [←hmodel] at hround
  exact hround

/-- Homogeneity identifies the actual model deletion in the current
local unit. This is the same D used in the retained physical path. -/
theorem node_model_deletion_identity :
    pathDeletion j.val N.coordinates/N.unit =
      (planeGap (innerStage j.val).price (innerStage j.val).intercept
        (innerStage j.val).lam N.plane (∑i : N.slots,C.originalWeight i/N.unit)+
        6*(innerStage j.val).intercept*(modelAmplification j N.coordinates/N.unit))/
          (6*(innerStage j.val).price) := by
  have hform : pathDeletion j.val N.coordinates =
      (modelCap j N.coordinates+(6*(innerStage j.val).price-1)*modelSlots j N.coordinates-
        (innerStage j.val).intercept*modelUnit j N.coordinates+
        6*(innerStage j.val).intercept*modelAmplification j N.coordinates)/
          (6*(innerStage j.val).price) := by
    fin_cases j <;> norm_num only [innerStage,Cycle153.FixedStages.stage4,div_one] <;> rfl
  have hslots : (∑i : N.slots,C.originalWeight i/N.unit)=modelSlots j N.coordinates/N.unit := by
    rw [←Finset.sum_div,N.slots_eq]
  have hplane : rawPlane j N.coordinates=modelPlane j N.coordinates := by
    fin_cases j <;> rfl
  rw [hform,modelCap_identity,hplane,N.plane_eq,hslots,←N.unit_eq]
  unfold planeGap
  field_simp [ne_of_gt N.unit_pos,ne_of_gt (innerStage j.val).price_pos]
  <;> ring

/-- The detector's rounded target has an explicit finite surcharge.
It is not identified with the model deletion, and its further whole-slot
mesh surcharge is paid separately by the native LOW source. -/
theorem actual_node_deletion_bounds :
    let S := innerStage j.val
    let actualDeletion := (planeGap S.price S.intercept S.lam N.position.B N.position.slotTop+
      6*S.intercept*S.amp N.position)/(6*S.price)
    pathDeletion j.val N.coordinates/N.unit ≤ actualDeletion ∧
      actualDeletion ≤ pathDeletion j.val N.coordinates/N.unit+2200*(1/C.gridDenominator) := by
  intro S actualDeletion
  have hI : (0:ℝ) ≤ S.intercept ∧ S.intercept ≤ 1 := by
    fin_cases j <;> norm_num [S,innerStage,Cycle153.FixedStages.stage1,
      Cycle153.FixedStages.stage2,Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4]
  have hg : (0:ℝ)<1/C.gridDenominator := by
    have hn : (0:ℝ)<C.gridDenominator := by exact_mod_cast C.grid_positive
    positivity
  have hd := Cycle153.rounded_deletion_bounds S
    (g:=1/C.gridDenominator) (B:=N.plane)
    (n1:=length N.localBase N.X1) (n2:=length N.localBase N.X2)
    (z:=∑i : N.slots,C.originalWeight i/N.unit)
    hg (inner_stage_ratio j) hI.1 hI.2
  change _ ∧ _ at hd
  rw [←N.rounded] at hd
  rw [←node_model_amplifier_identity N] at hd
  rw [←node_model_deletion_identity N] at hd
  exact hd

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_node_amp_bounds

#print axioms OAI.SevenEighths.Cycle153Reachable.actual_node_deletion_bounds
