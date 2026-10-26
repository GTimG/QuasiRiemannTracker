/- Literal scheduled fee and raw selected source weight. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeScheduledRawWeight
import Candidate.Research.RecursiveAffine.NativeChosenRawBinding
import Candidate.Research.RecursiveAffine.NativeColumnTraceGraft

set_option autoImplicit false
set_option linter.unusedVariables false
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
variable {hH : RayOrthogonality.globalUnits M  ≤  H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- Bind the real selected-source arithmetic edge to the native analytic
row weight. The edge is the one already transferred to the EXACT Columns
child; the paid node and scheduled fee are retained by their literal
identities. This derives rawWeight and rawMissing for the trace graft,
without any count, energy or alternate output. -/
theorem actual_literal_edge_chosen_column (N : ReachableNode C j)(hj : j.val<3)
    (reflected second : Bool)(s : Input N.slots)(R seed : Ideal O)
    (Mrow amp xi reserve epsRow b firstHeight : ℝ)(n : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (N.localBase^Mrow)
      N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume s))
      (geometryFirstLabel s R seed (N.localBase^Mrow) N.localBase xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val)  ≤  sideError)
    (r : NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight n
      N.localBase_gt_one key hz1 hz2 firstIndex)
    (eps : ℝ)(budget : ℕ)(Rd : Finset N.slots)
    (hdeleted : (∑i∈Rd,C.originalWeight i/N.unit)  ≤  nodeDetectorDeletion N+C.slotMesh)
    (deleted : (NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight n
      N.localBase_gt_one key hz1 hz2 firstIndex)→Finset N.slots)
    (hdeletedRow : deleted r=Rd) :
    let paid:=fun rr=>actualSelectedPaidNode N reflected second s R seed Mrow amp xi reserve epsRow b firstHeight n
      key hz1 hz2 firstIndex massLoss sideError hside rr
    let node:=paid r
    let fee:=actualNodeGlobalFee (hH:=hH) N eps budget Rd hdeleted
    let weight:=fun rr=>N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second
      (paid rr).first (paid rr).C (paid rr).D (paid rr).inactive N.localBase Mrow (Real.logb N.localBase (volume s))
      amp xi reserve epsRow 0+(innerStage j.val).q*(∑i∈deleted rr,C.originalWeight i/N.unit)+massLoss+
      actualInnerRemainingFees (hH:=hH) N eps budget)
    let missing:=fun rr=>Real.logb N.localBase ((firstSourceMissing (!reflected) (paid rr).first).absNorm:ℝ)
    ∀(units : FirstSourceLabel→O)(child : ReachableNode C (nextInner j hj))
      (hu : child.unit  ≤  N.unit)
      (hroot : child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) N.presentation.mult units
        (nativeLowHistoryCode reflected s R seed N.localBase Mrow amp xi reserve b firstHeight n
          N.localBase_gt_one key hz1 hz2 firstIndex r).1)
      (edge : NativeTraceEdge (hH:=hH) N child.coordinates
        (child.unit*child.state.rowWidth)
        (child.unit*Real.logb child.localBase (volume (child.input hH)))
        (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ)))
      (hnode : edge.node=node)(hfee : edge.fee=fee)
      (constant childEps Bsrc : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)
      (boxes : ℕ→Finset (Fin 4→ℤ))
      (out : NodeOutput hH child constant childEps Bsrc control degree (fun k=>boxes (k+1)))
      (rawRoot : (NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight n
        N.localBase_gt_one key hz1 hz2 firstIndex)→O)
      (rawFamily : (rr : NativeLowRows reflected s R seed N.localBase Mrow amp xi reserve b firstHeight n
        N.localBase_gt_one key hz1 hz2 firstIndex)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
        C.etaSeed N.localBase C.Bnorm C.Tz (rawRoot rr))
      (hvalue : (rawFamily r).value=out.family.value),
    Nonempty (ChosenInnerColumn N hj reflected s R seed Mrow amp xi reserve b firstHeight n
      key hz1 hz2 firstIndex units weight missing Bsrc boxes rawRoot rawFamily r) :=by
  intro paid node fee weight missing units child hu hroot edge hnode hfee constant childEps Bsrc control degree boxes
    out rawRoot rawFamily hvalue
  have raw:=actual_chosen_column_scheduled_arithmetic N reflected second s R seed Mrow amp xi reserve epsRow b
    firstHeight n key hz1 hz2 firstIndex massLoss sideError hside r eps budget Rd hdeleted child edge hnode hfee
  refine ⟨{
    child:=child, unit:=hu, root:=hroot, constant:=constant, epsilon:=childEps, control:=control,
    degree:=degree, output:=out, edge:=edge, rawWeight:=?_, rawMissing:=raw.2, value:=hvalue }⟩
  change N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
    N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve epsRow 0+
    (innerStage j.val).q*(∑i∈deleted r,C.originalWeight i/N.unit)+massLoss+
    actualInnerRemainingFees (hH:=hH) N eps budget)=_
  rw [hdeletedRow]
  exact raw.1

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_literal_edge_chosen_column
