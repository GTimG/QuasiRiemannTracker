/- Keep the actual Columns child/output while transporting its arithmetic edge.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualTraceAttach
import Candidate.Research.RecursiveAffine.ActualTraceTerminal

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentAmplificationChildInput
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j k : Fin 4}

/-- The Columns producer has already selected its concrete continuation
child and NodeOutput. Transfer the actual source edge onto that SAME child
using the literal coordinate, global-row and prefix identities. Actual
volume is fixed by those same coordinates. All source/fee fields remain
literal, so the raw physical source weight is unchanged. -/
def NativeTraceEdge.atChosenChild (parent : ReachableNode C j)
    (constructed chosen : ReachableNode C k)
    (edge : NativeTraceEdge (hH:=hH) parent constructed.coordinates
      (constructed.unit*constructed.state.rowWidth)
      (constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH)))
      (Real.logb C.globalBase ((Ideal.span {constructed.presentation.mult}).absNorm:ℝ)))
    (hcoordinates : constructed.coordinates=chosen.coordinates)
    (hrow : constructed.unit*constructed.state.rowWidth=chosen.unit*chosen.state.rowWidth)
    (hroot : constructed.presentation.mult=chosen.presentation.mult) :
    NativeTraceEdge (hH:=hH) parent chosen.coordinates
      (chosen.unit*chosen.state.rowWidth)
      (chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH)))
      (Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)) := by
  have hvolume : constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH))=
      chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH)) := by
    rw [constructed.volume_model,chosen.volume_model,hcoordinates]
  exact {
    node:=edge.node,fee:=edge.fee,sourceGates:=edge.sourceGates,fineSource:=edge.fineSource,
    fineFee:=edge.fineFee,remainingFee:=edge.remainingFee,V:=edge.V,Red:=edge.Red,
    residualF:=edge.residualF,residualF_nonneg:=edge.residualF_nonneg,
    capacityPad:=edge.capacityPad,scalePad:=edge.scalePad,amplifierError:=edge.amplifierError,
    amplifierError_nonneg:=edge.amplifierError_nonneg,fineAmplifierError:=edge.fineAmplifierError,
    fineScalePad:=edge.fineScalePad,fineCapacityPad:=edge.fineCapacityPad,
    root_scale:=edge.root_scale,root_length:=edge.root_length,
    relative_scale:=by rw [←hrow,←hroot];exact edge.relative_scale,
    length_step:=by rw [←hvolume];exact edge.length_step,
    capacity:=by rw [←hvolume];exact edge.capacity,
    prefix_preserved:=by simpa only [hcoordinates] using edge.prefix_preserved,
    length_model:=by simpa only [hcoordinates] using edge.length_model,
    unit_model:=by simpa only [hcoordinates] using edge.unit_model,
    junction_model:=edge.junction_model,
    deletion_model:=by simpa only [hcoordinates] using edge.deletion_model,
    missing_model:=by simpa only [hcoordinates] using edge.missing_model,
    reduction_model:=by simpa only [hcoordinates] using edge.reduction_model,
    amplifier_model:=by simpa only [hcoordinates] using edge.amplifier_model }

@[simp] theorem NativeTraceEdge.atChosenChild_node (parent : ReachableNode C j)
    (constructed chosen : ReachableNode C k)
    (edge : NativeTraceEdge (hH:=hH) parent constructed.coordinates
      (constructed.unit*constructed.state.rowWidth)
      (constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH)))
      (Real.logb C.globalBase ((Ideal.span {constructed.presentation.mult}).absNorm:ℝ)))
    (hcoordinates : constructed.coordinates=chosen.coordinates)
    (hrow : constructed.unit*constructed.state.rowWidth=chosen.unit*chosen.state.rowWidth)
    (hroot : constructed.presentation.mult=chosen.presentation.mult) :
    (edge.atChosenChild parent constructed chosen hcoordinates hrow hroot).node=edge.node :=rfl

@[simp] theorem NativeTraceEdge.atChosenChild_fee (parent : ReachableNode C j)
    (constructed chosen : ReachableNode C k)
    (edge : NativeTraceEdge (hH:=hH) parent constructed.coordinates
      (constructed.unit*constructed.state.rowWidth)
      (constructed.unit*Real.logb constructed.localBase (volume (constructed.input hH)))
      (Real.logb C.globalBase ((Ideal.span {constructed.presentation.mult}).absNorm:ℝ)))
    (hcoordinates : constructed.coordinates=chosen.coordinates)
    (hrow : constructed.unit*constructed.state.rowWidth=chosen.unit*chosen.state.rowWidth)
    (hroot : constructed.presentation.mult=chosen.presentation.mult) :
    (edge.atChosenChild parent constructed chosen hcoordinates hrow hroot).fee=edge.fee :=rfl

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.NativeTraceEdge.atChosenChild
