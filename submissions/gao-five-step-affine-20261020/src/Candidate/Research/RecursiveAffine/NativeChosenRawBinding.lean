/- Literal scheduled fee and raw selected source weight. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeScheduledRawWeight
import Candidate.Research.RecursiveAffine.NativeColumnTraceGraft

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization Cycle153Reachable Cycle153JointCount Cycle153SourceSchedule
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- Bind the real selected-source arithmetic edge to the native analytic
row weight. The edge is the one already transferred to the EXACT Columns
child; the paid node and scheduled fee are retained by their literal
identities. This derives rawWeight and rawMissing for the trace graft,
without any count, energy or alternate output. -/
theorem actual_chosen_column_scheduled_arithmetic (N : ReachableNode C j)
    (reflected second : Bool)(s : Input N.slots)(R seed : Ideal O)
    (Mrow amp xi reserve epsRow b firstHeight : ℝ)(n : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (N.localBase^Mrow)
      N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume s))
      (geometryFirstLabel s R seed (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (r : NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight n
      N.localBase_gt_one key hz1 hz2 firstIndex)
    (eps : ℝ)(budget : ℕ)(Rd : Finset N.slots)
    (hdeleted : (∑i∈Rd,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+C.slotMesh) :
    let node:=actualSelectedPaidNode N reflected second s R seed Mrow amp xi reserve epsRow b firstHeight n
      key hz1 hz2 firstIndex massLoss sideError hside r
    let fee:=actualNodeGlobalFee (hH:=hH) N eps budget Rd hdeleted
    ∀{k : Fin 4}(child : ReachableNode C k)
      (edge : NativeTraceEdge (hH:=hH) N child.coordinates
        (child.unit*child.state.rowWidth)
        (child.unit*Real.logb child.localBase (volume (child.input hH)))
        (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ))),
    edge.node=node → edge.fee=fee →
    N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
      N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve epsRow 0+
      (innerStage j.val).q*(∑i∈Rd,C.originalWeight i/N.unit)+massLoss+
      actualInnerRemainingFees (hH:=hH) N eps budget)=
    C.globalBase^(edge.node.scale+edge.node.shiftedOutside+edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount) ∧
    edge.node.coordinate 1=N.unit*Real.logb N.localBase
      ((firstSourceMissing (!reflected) node.first).absNorm:ℝ) := by
  intro node fee k child edge hnode hfee
  constructor
  · rw [hnode,hfee]
    exact actual_selected_scheduled_raw_weight N reflected second s R seed Mrow amp xi reserve epsRow b
      firstHeight n key hz1 hz2 firstIndex massLoss sideError hside r eps budget Rd hdeleted
  · rw [hnode]
    exact actual_selected_paid_node_missing N reflected second s R seed Mrow amp xi reserve epsRow b
      firstHeight n key hz1 hz2 firstIndex massLoss sideError hside r

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_chosen_column_scheduled_arithmetic
