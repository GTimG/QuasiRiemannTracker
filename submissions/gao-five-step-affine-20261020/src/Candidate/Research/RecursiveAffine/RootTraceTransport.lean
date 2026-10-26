/- Preserve the genuine root edge while deeper coordinates are appended. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootReturnedPayment

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily Cycle153Geometry
variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {C : SourceContext (α:=α) M H}

/-- A deeper attaining source keeps the literal initial root data.
Only future coordinates may change; no equality of the whole vectors
is imposed on the recursive output. -/
def RootTraceEdge.transportFinal {x y : Fin 14→ℝ} {m A v : ℝ}
    (edge : RootTraceEdge (C:=C) x m A v)
    (agree : ∀i,prefixCoordinate 1 i→y i=x i) :
    RootTraceEdge (C:=C) y m A v := by
  have h0:=agree 0 (by norm_num [prefixCoordinate])
  have h1:=agree 1 (by norm_num [prefixCoordinate])
  have h5:=agree 5 (by norm_num [prefixCoordinate])
  have hA : Coordinates.upperRootLength1 y=Coordinates.upperRootLength1 x := by
    simp only [Coordinates.upperRootLength1,Coordinates.b,h0]
  have ha : Coordinates.a0 y=Coordinates.a0 x := by
    simp only [Coordinates.a0,Coordinates.gap0,Coordinates.b,Coordinates.U0,h0]
  have hd : Coordinates.d0 y=Coordinates.d0 x := by
    simp only [Coordinates.d0,Coordinates.gap0,Coordinates.b,h0,ha]
  refine {
    node:=edge.node
    unit_eq:=edge.unit_eq
    fee:=edge.fee
    sourceGates:=edge.sourceGates
    fineSource:=edge.fineSource
    fineFee:=edge.fineFee
    remainingFee:=edge.remainingFee
    V:=edge.V
    Red:=edge.Red
    residualF:=edge.residualF
    residualF_nonneg:=edge.residualF_nonneg
    capacityPad:=edge.capacityPad
    scalePad:=edge.scalePad
    root_scale:=edge.root_scale
    root_length:=by rw [hA];exact edge.root_length
    relative_scale:=edge.relative_scale
    length_step:=edge.length_step
    capacity:=edge.capacity
    junction_model:=edge.junction_model
    deletion_model:=by rw [hd];exact edge.deletion_model
    missing_model:=by simpa only [Coordinates.V0,h1] using edge.missing_model
    reduction_model:=by simpa only [Coordinates.Red0,h5] using edge.reduction_model
    amplifierError:=edge.amplifierError
    amplifierError_nonneg:=edge.amplifierError_nonneg
    fineAmplifierError:=edge.fineAmplifierError
    fineScalePad:=edge.fineScalePad
    fineCapacityPad:=edge.fineCapacityPad
    amplifier_model:=by rw [ha];exact edge.amplifier_model }

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.RootTraceEdge.transportFinal
