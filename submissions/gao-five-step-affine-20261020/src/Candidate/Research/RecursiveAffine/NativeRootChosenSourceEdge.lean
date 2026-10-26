/- Keep the actual Columns root child/output and its literal source edge.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeActualRootSourceEdge

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentAmplificationChildInput
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}

/-- The actual source has already chosen its concrete child/output.
Arithmetic coordinate, row and prefix identities transport the actual
constructed root edge to that SAME child, preserving node and fee. -/
def RootTraceEdge.atChosenChild (constructed chosen : ReachableNode C 0)
    (edge : RootTraceEdge (C:=C) constructed.coordinates
      (constructed.unit*constructed.state.rowWidth)
      (constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH)))
      (Real.logb C.globalBase ((Ideal.span {constructed.presentation.mult}).absNorm:ℝ)))
    (hcoordinates : constructed.coordinates=chosen.coordinates)
    (hrow : constructed.unit*constructed.state.rowWidth=chosen.unit*chosen.state.rowWidth)
    (hroot : constructed.presentation.mult=chosen.presentation.mult) :
    RootTraceEdge (C:=C) chosen.coordinates
      (chosen.unit*chosen.state.rowWidth)
      (chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH)))
      (Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)) :=by
  have hvolume : constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH))=
      chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH)) :=by
    rw [constructed.volume_model,chosen.volume_model,hcoordinates]
  exact {
    node:=edge.node,unit_eq:=edge.unit_eq,fee:=edge.fee,sourceGates:=edge.sourceGates,fineSource:=edge.fineSource,
    fineFee:=edge.fineFee,remainingFee:=edge.remainingFee,V:=edge.V,Red:=edge.Red,
    residualF:=edge.residualF,residualF_nonneg:=edge.residualF_nonneg,
    capacityPad:=edge.capacityPad,scalePad:=edge.scalePad,
    root_scale:=edge.root_scale,root_length:=by simpa only [hcoordinates] using edge.root_length,
    relative_scale:=by rw [←hrow,←hroot];exact edge.relative_scale,
    length_step:=by rw [←hvolume];exact edge.length_step,
    capacity:=by rw [←hvolume];exact edge.capacity,
    junction_model:=edge.junction_model,deletion_model:=by simpa only [hcoordinates] using edge.deletion_model,
    missing_model:=by simpa only [hcoordinates] using edge.missing_model,
    reduction_model:=by simpa only [hcoordinates] using edge.reduction_model,
    amplifierError:=edge.amplifierError,amplifierError_nonneg:=edge.amplifierError_nonneg,
    fineAmplifierError:=edge.fineAmplifierError,fineScalePad:=edge.fineScalePad,
    fineCapacityPad:=edge.fineCapacityPad,amplifier_model:=by simpa only [hcoordinates] using edge.amplifier_model }

@[simp] theorem RootTraceEdge.atChosenChild_node (constructed chosen : ReachableNode C 0)
    (edge : RootTraceEdge (C:=C) constructed.coordinates
      (constructed.unit*constructed.state.rowWidth)
      (constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH)))
      (Real.logb C.globalBase ((Ideal.span {constructed.presentation.mult}).absNorm:ℝ)))
    (hcoordinates : constructed.coordinates=chosen.coordinates)
    (hrow : constructed.unit*constructed.state.rowWidth=chosen.unit*chosen.state.rowWidth)
    (hroot : constructed.presentation.mult=chosen.presentation.mult) :
    (edge.atChosenChild constructed chosen hcoordinates hrow hroot).node=edge.node :=rfl

@[simp] theorem RootTraceEdge.atChosenChild_fee (constructed chosen : ReachableNode C 0)
    (edge : RootTraceEdge (C:=C) constructed.coordinates
      (constructed.unit*constructed.state.rowWidth)
      (constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH)))
      (Real.logb C.globalBase ((Ideal.span {constructed.presentation.mult}).absNorm:ℝ)))
    (hcoordinates : constructed.coordinates=chosen.coordinates)
    (hrow : constructed.unit*constructed.state.rowWidth=chosen.unit*chosen.state.rowWidth)
    (hroot : constructed.presentation.mult=chosen.presentation.mult) :
    (edge.atChosenChild constructed chosen hcoordinates hrow hroot).fee=edge.fee :=rfl
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.RootTraceEdge.atChosenChild
