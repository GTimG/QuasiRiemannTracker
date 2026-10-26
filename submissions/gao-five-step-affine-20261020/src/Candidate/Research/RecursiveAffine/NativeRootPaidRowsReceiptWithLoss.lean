/- Whole ROOT row families retain their actual one-column paid outputs.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootColumnPaidResult
import Candidate.Research.RecursiveAffine.NativeRootColumnReceiptWithLoss
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsChoice
import Candidate.Research.RecursiveAffine.NativeRootPaidSource
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153JointCount Cycle153RegionalLow Cycle153RootStep Cycle153SourceReturn Cycle153Geometry
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}{C : SourceContext (α:=alpha) M H}

/-- A pointwise actual source result becomes the literal whole-row
chosen-source interface. Every edge/output/family is copied from that
same result; no depth or component is maximized independently. -/
theorem actual_root_receipt_from_paid_rows_with_loss
    (s : Input alpha)(reflected second : Bool)(epsRow firstHeight massLoss sideError : ℝ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (Cycle153SourceSchedule.nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
    (hside : ∀l,massLoss+lowLabelSide reflected C.globalBase (Real.logb C.globalBase (volume s))
      (geometryFirstLabel s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (Cycle153SourceSchedule.nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val)≤ sideError)
    (units : FirstSourceLabel→O)(epsNode : ℝ)(feeBudget : ℕ)(mesh : ℝ)(hmesh : 0≤ mesh)
    (constant epsilon Bsrc : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)(boxes : ℕ→Finset (Fin 4→ℤ)) :
    let Rows:=NativeLowRows reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8) (9/4) firstHeight
      (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
    let rowKey:=nativeLowHistoryCode reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8) (9/4) firstHeight
      (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
    let paid:=fun r : Rows=>actualRootSelectedPaidNode C.globalBase C.globalBase_gt_one reflected second s 1 1 1
      (rootSourceAmp C.originalWeight) (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8)
      epsRow (9/4) firstHeight (Fintype.card alpha) key hz1 hz2 firstIndex massLoss sideError hside r
    ∀(rawRoot : Rows→O)(hroot : ∀r,rawRoot r=Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1)
      (energy fixed old : Rows→ℝ)(coefficient : Rows→Finset alpha→ℝ)
      (result : ∀r,RootColumnPaidResult (hH:=hH) C s (paid r) epsNode feeBudget mesh hmesh
        (rawRoot r) constant epsilon Bsrc control degree (fun k=>boxes (k+1))
        (energy r) (fixed r) (old r) (coefficient r)),
    ∀(hBsrc : 0≤Bsrc)
      (hfirst : Function.Injective (fun l=>(geometryFirstLabel s 1 1 (C.globalBase^(1:ℝ)) C.globalBase
        (Cycle153SourceSchedule.nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _)
        key (firstIndex l).1.val,(firstIndex l).1.val.2.1.val)))
      (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
        C.globalBase Bsrc (boxes 0) ((),rowKey r)),
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
      (∀d p,(receipt.family.part d p).loss≤5/1000000000000) ∧
      receipt.family.value=∑r : Rows,C.globalBase^(1+actualHighCoordinates reflected (!reflected) second
        (geometryFirstLabel s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (Cycle153SourceSchedule.nativeMu/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex r.val.1).1.val)
        (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 C.globalBase 1
        (Real.logb C.globalBase (volume s)) (rootSourceAmp C.originalWeight)
        (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8) epsRow 0+
        Coordinates.q0*(∑i∈(result r).deleted,C.originalWeight i)+
        (massLoss+actualRootRemainingFeesAtMesh C s epsNode feeBudget mesh))*(result r).family.value :=by
  intro Rows rowKey paid rawRoot hroot energy fixed old coefficient result hBsrc hfirst sourceFacts
  have chosen:=actual_root_paid_rows_to_choices s reflected second epsRow firstHeight massLoss sideError
    key hz1 hz2 firstIndex hside units epsNode feeBudget mesh hmesh constant epsilon Bsrc control degree boxes
    rawRoot hroot energy fixed old coefficient result
  exact actual_root_receipt_from_chosen_columns_with_loss reflected second s 1 1 1 (rootSourceAmp C.originalWeight)
    (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8) epsRow (9/4) firstHeight
    (Fintype.card alpha) key hz1 hz2 firstIndex units C.originalWeight (fun r=>(result r).deleted)
    Coordinates.q0 (fun _=>massLoss+actualRootRemainingFeesAtMesh C s epsNode feeBudget mesh)
    rawRoot (fun r=>(result r).family) Bsrc boxes hBsrc hfirst sourceFacts chosen
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_root_receipt_from_paid_rows_with_loss
