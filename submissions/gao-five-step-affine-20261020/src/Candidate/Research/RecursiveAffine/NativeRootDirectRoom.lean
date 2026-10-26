/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootStep

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OAI.SevenEighths.Cycle153RootStep
noncomputable section
open Cycle63.Optimization Cycle153.MarkedRootPrice Cycle153Geometry

/-- Native direct-deletion room of the true original cell. The old
slot price remains distinct from the marked affine amplifier price. -/
def rootDirectRoom (b : ℝ) : ℝ :=
  (q/(6*slotPrice))*((1-2*Coordinates.mu)-planeGap slotPrice 1 lambda B b)+
    planeAmplifier price intercept q lambda B b*(1-12*(q/(6*slotPrice)))-
      lowReserveAt price intercept q

/-- Every original cell leaves direct room; no first-inner ledger or
future source inequality is needed for the narrow-root branch. -/
theorem root_direct_room (b : ℝ) (hlo : Cycle153.Root.floor+Cycle153.Root.mesh ≤ b)
    (hhi : b ≤ Cycle153.MarkedRootPrice.top) :
    (1/1000000000:ℝ) ≤ rootDirectRoom b := by
  have hp:=price_bounds
  have hi:=intercept_bounds
  have hq:=q_bounds
  have hl:=lambda_bounds
  have hB:=B_bounds
  unfold rootDirectRoom
  simp only [planeGap,planeAmplifier,amplifierRatio,lowReserveAt,lowReserveWeight,
    allowanceUnit,slotPrice,betaBound,Coordinates.mu]
  norm_num only [Cycle153.Root.floor,Cycle153.Root.mesh,Cycle153.MarkedRootPrice.top] at hlo hhi
  have hb : b∈Set.Icc (3400001/100000000:ℝ) (2019049/50000000:ℝ):=⟨hlo,hhi⟩
  apply le_of_lt
  rat_pos (depth:=30) [hp,hi,hq,hl,hB,hb]

end
end OAI.SevenEighths.Cycle153RootStep
#print axioms OAI.SevenEighths.Cycle153RootStep.root_direct_room
