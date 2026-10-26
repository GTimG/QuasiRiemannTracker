/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeColumnReceiptGraft
import Candidate.Research.RecursiveAffine.NativeInnerReceiptLossRoom

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization Cycle153SourceReturn Cycle153Reachable Cycle153JointCount
variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (parent : ReachableNode C j)(hj : j.val<3)
variable (reflected second : Bool)(s : Input parent.slots)(R seed : Ideal O)
variable (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
variable (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (parent.localBase^Mrow)
  parent.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans parent.localBase_gt_one) _) key)
local notation "Rows"=>NativeLowRows reflected s R seed parent.localBase Mrow amp xi reserve b firstHeight
  budget parent.localBase_gt_one key hz1 hz2 firstIndex
local notation "first"=>fun l=>geometryFirstLabel s R seed (parent.localBase^Mrow) parent.localBase xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans parent.localBase_gt_one) _) key (firstIndex l).1.val
local notation "rowKey"=>nativeLowHistoryCode reflected s R seed parent.localBase Mrow amp xi reserve b firstHeight
  budget parent.localBase_gt_one key hz1 hz2 firstIndex

/-- Attach the entire actual selected-row family coming from the
chosen native Column traces. Every child receipt is derived from the
SAME deeper output and real arithmetic edge; the resulting licensed
whole receipt has exactly the analytic raw weighted family value. No
energy or returned-count premise is used in this attachment. -/
theorem actual_inner_shell_receipt_from_chosen_columns
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz parent.presentation.mult)
    (w : parent.slots→ℝ)(deleted : Rows→Finset parent.slots)(q : ℝ)(fees : Rows→ℝ)
    (rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz (rawRoot r))
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(hBsrc : 0 ≤ Bsrc)
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>parent.presentation.mult) (!reflected)
      (fun _=>units) parent.localBase Bsrc (boxes 0) ((),rowKey r))
    (hm : own.scale=parent.state.rowWidth)
    (hA : own.length=Real.logb parent.localBase (volume (parent.input hH)))
    (ha : letI : Cycle63.AffineLedger:=parent.ledger
      own.amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : parent.slots,C.originalWeight i/parent.unit))))
    (ampError : ℝ)(hAmp0 : 0 ≤ ampError)(hAmpFine : ampError ≤ 1/1000000000000)
    (hAmp : parent.unit*own.amp ≤
      ![Cycle153Geometry.Coordinates.a1 parent.coordinates,Cycle153Geometry.Coordinates.a2 parent.coordinates,
        Cycle153Geometry.Coordinates.a3 parent.coordinates,Cycle153Geometry.Coordinates.a4 parent.coordinates] j+ampError)
    (ownLoss : own.loss ≤ terminalLossCap j)
    (ownClass : ∀b,(Fintype.card (own.record b).Class:ℝ) ≤ C.highClassCap)
    (chosen : ∀r,rawFamily r=emptyReturnedForest ∨ Nonempty (ChosenInnerColumn parent hj reflected
      s R seed Mrow amp xi reserve b firstHeight budget key hz1 hz2 firstIndex units
      (fun r=>parent.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
        (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 parent.localBase Mrow
        (Real.logb parent.localBase (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r)) (fun r=>Real.logb parent.localBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)) Bsrc boxes rawRoot rawFamily r))
    (shift : ℝ)(hshift : shift ≤ 1/1000000000000)
    (ownRoom : own.loss+shift ≤ terminalLossCap j) :
    ∃receipt : NativeNodeForestReceipt hH parent Bsrc boxes,
      receipt.family.value=own.value+∑r : Rows,parent.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
        (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 parent.localBase Mrow
        (Real.logb parent.localBase (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r)*(rawFamily r).value ∧
      ∀d p,(receipt.family.part d p).loss+shift ≤ terminalLossCap j := by
  obtain ⟨children,hvalue,hsources⟩:=actual_columns_to_inner_source_choices parent hj reflected
    s R seed Mrow amp xi reserve b firstHeight budget key hz1 hz2 firstIndex units
    (fun r=>parent.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
        (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 parent.localBase Mrow
        (Real.logb parent.localBase (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r)) (fun r=>Real.logb parent.localBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)) Bsrc boxes rawRoot rawFamily chosen
  let receipt:=actual_native_inner_source_receipt parent hj reflected second s R seed Mrow amp xi reserve eps b
    firstHeight budget key hz1 hz2 firstIndex units own w deleted q fees children Bsrc boxes hBsrc
    hfirst sourceFacts hm hA ha ampError hAmp0 hAmpFine hAmp ownLoss ownClass hsources
  refine ⟨receipt,?_,?_⟩
  swap
  · exact actual_native_inner_source_receipt_loss_room parent hj reflected second s R seed Mrow amp xi reserve eps b
      firstHeight budget key hz1 hz2 firstIndex units own w deleted q fees children Bsrc boxes hBsrc hfirst
      sourceFacts hm hA ha ampError hAmp0 hAmpFine hAmp ownLoss ownClass hsources shift hshift ownRoom
  change (actualNativeSuffixRows parent hj reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex units own w deleted q fees children).value=_
  rw [actualNativeSuffixRows_value]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [hvalue r]

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_inner_shell_receipt_from_chosen_columns
