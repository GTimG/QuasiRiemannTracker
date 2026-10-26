/- Literal scheduled fee and raw selected source weight. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedRawFields
import Candidate.Research.RecursiveAffine.ActualNodeNativeFee

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

/-- Every non-mass-loss fee in the actual native selected-row weight.
Actual deletion stays outside; only the explicitly paid mesh appears
here. The first-mass loss remains in the SAME paid node's shifted X0. -/
def actualInnerRemainingFees (N : ReachableNode C j)(eps : ℝ)(budget : ℕ) : ℝ :=
  3*nativeDriverRate budget+oldLoss eps+postDictionaryRate C.Bnorm budget+
    130*postDictionaryRate C.Bnorm budget+actualNodeLocalSourcePad (hH:=hH) N+
    2*nativeDriverRate budget*31*(Fintype.card N.slots:ℝ)+(innerStage j.val).q*C.slotMesh

/-- The exact global raw edge uses the actual native scheduled fee once.
The source's actual deleted weight, native rounded target and model
threshold remain distinct. No leading deletion or mass term is dropped. -/
theorem actual_selected_scheduled_raw_weight (N : ReachableNode C j)
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
    N.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second node.first node.C node.D node.inactive
      N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve epsRow 0+
      (innerStage j.val).q*(∑i∈Rd,C.originalWeight i/N.unit)+massLoss+
      actualInnerRemainingFees (hH:=hH) N eps budget)=
    C.globalBase^(node.scale+node.shiftedOutside+fee.junction*fee.modelDeletion+fee.amount) := by
  intro node fee
  have h:=actual_selected_raw_edge_global N reflected second s R seed Mrow amp xi reserve epsRow b firstHeight n
    key hz1 hz2 firstIndex massLoss sideError hside r (innerStage j.val).q
    (∑i∈Rd,C.originalWeight i/N.unit) (pathDeletion j.val N.coordinates/N.unit)
    (actualInnerRemainingFees (hH:=hH) N eps budget)
  have hcancel : N.unit*(pathDeletion j.val N.coordinates/N.unit)=pathDeletion j.val N.coordinates :=by
    field_simp [N.unit_pos.ne']
  dsimp only at h
  rw [hcancel] at h
  apply h.trans
  congr 1
  change node.scale+node.shiftedOutside+(innerStage j.val).q*pathDeletion j.val N.coordinates+
      N.unit*(actualInnerRemainingFees (hH:=hH) N eps budget+
        (innerStage j.val).q*((∑i∈Rd,C.originalWeight i/N.unit)-pathDeletion j.val N.coordinates/N.unit))=
    node.scale+node.shiftedOutside+fee.junction*fee.modelDeletion+fee.amount
  have hmodel:=actual_node_fee_model (hH:=hH) N eps budget Rd hdeleted
  have hamount:=actual_node_fee_amount (hH:=hH) N eps budget Rd hdeleted
  have hq : fee.junction=(innerStage j.val).q:=rfl
  change fee.modelDeletion=_ at hmodel
  change fee.amount=_ at hamount
  rw [hq,hmodel,hamount]
  dsimp only [actualInnerRemainingFees]
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_scheduled_raw_weight
