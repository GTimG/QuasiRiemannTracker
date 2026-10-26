/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalStageSchedule

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Cycle153.RegionalSchedule
noncomputable section
open Cycle63.Optimization

/-- The analytic tolerance fixes the native loss unit. It is independent
of the much finer coordinate grid and pays the actual detector surcharge. -/
def primitiveError : ℝ := 1/(10:ℝ)^14
def gridSize : ℕ := 10^40

theorem primitiveError_pos : 0<primitiveError := by norm_num [primitiveError]
theorem gridSize_pos : 0<gridSize := by norm_num [gridSize]
theorem primitive_grid_exact : 1/(gridSize:ℝ)=1/(10:ℝ)^40 := by norm_num [gridSize]
theorem primitive_grid : 1/(gridSize:ℝ)≤primitiveError := by norm_num [gridSize,primitiveError]

/-- The analytic primitive loss is inside every fixed stage reserve. Thus the
actual native loss unit at all five stages is literally the same rational,
although the regional junctions and planes differ. -/
theorem primitive_stageMu (j : Fin 5) :
    stageMu (stage j) primitiveError=primitiveError/128 := by
  fin_cases j <;>
    norm_num [stageMu,stage,primitiveError,lowReserveAt,lowReserveWeight,allowanceUnit,
      FixedStages.stage0,FixedStages.stage1,FixedStages.stage2,FixedStages.stage3,FixedStages.stage4]

theorem primitive_marked_cap (j : Fin 5) :
    stageMu (stage j) primitiveError≤geometryLossCap := by
  rw [primitive_stageMu j]
  norm_num [primitiveError,geometryLossCap,lowReserveWeight,allowanceUnit,
    slotPrice,betaBound,planeQuadratic]

/-- Grid choice and native analytic schedule are fixed before all moving
rounded source coordinates. This does not enumerate the grid. -/
theorem primitive_native_mu (j : Fin 5) (i : RegionalIndex (stage j) gridSize) :
    @OAI.SevenEighths.Cycle63InitialMass.geometryLossUnit (regionalFamily (stage j) gridSize i)
      1 primitiveError=primitiveError/128 :=
  (stageMu_eq_native (stage j) gridSize i primitiveError).trans (primitive_stageMu j)

end
end Cycle153.RegionalSchedule

#print axioms Cycle153.RegionalSchedule.primitive_stageMu
#print axioms Cycle153.RegionalSchedule.primitive_native_mu
#print axioms Cycle153.RegionalSchedule.primitive_marked_cap
