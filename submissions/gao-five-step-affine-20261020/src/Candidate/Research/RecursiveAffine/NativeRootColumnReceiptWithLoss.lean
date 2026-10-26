/- The SAME native Columns output supplies the root returned forest.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootColumnChoices
import Candidate.Research.RecursiveAffine.NativeRootReceiptLossRoom

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization Cycle153SourceReturn Cycle153Reachable Cycle153JointCount
open Cycle153ActualColumn
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}
variable (reflected second : Bool)(s : Input alpha)(R seed : Ideal O)
variable (Mrow amp xi reserve eps b firstHeight : ℝ)(budget : ℕ)
variable (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (C.globalBase^Mrow)
  C.globalBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
local notation "Rows"=>NativeLowRows reflected s R seed C.globalBase Mrow amp xi reserve b firstHeight
  budget C.globalBase_gt_one key hz1 hz2 firstIndex
local notation "first"=>fun l=>geometryFirstLabel s R seed (C.globalBase^Mrow) C.globalBase xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
local notation "rowKey"=>nativeLowHistoryCode reflected s R seed C.globalBase Mrow amp xi reserve b firstHeight
  budget C.globalBase_gt_one key hz1 hz2 firstIndex

/-- The entire actual root row carrier is attached once. Its arithmetic
receipt has exactly the analytic raw weighted value of the SAME chosen
Column outputs; there is no root moment or count input. -/
theorem actual_root_receipt_from_chosen_columns_with_loss
    (units : FirstSourceLabel→O)(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz (rawRoot r))
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(hBsrc : 0 ≤ Bsrc)
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
      C.globalBase Bsrc (boxes 0) ((),rowKey r))
    (chosen : ∀r,rawFamily r=emptyReturnedForest ∨ Nonempty (ChosenRootColumn reflected second
      s R seed Mrow amp xi reserve eps b firstHeight budget key hz1 hz2 firstIndex
      units w deleted q fees Bsrc boxes rawRoot rawFamily r)) :
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
      (∀d p,(receipt.family.part d p).loss≤5/1000000000000) ∧
      receipt.family.value=∑r : Rows,C.globalBase^(Mrow+actualHighCoordinates reflected (!reflected) second
        (first r.val.1) (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 C.globalBase Mrow
        (Real.logb C.globalBase (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r)*(rawFamily r).value :=by
  obtain ⟨children,hvalue,hsources⟩:=actual_columns_to_root_source_choices reflected second s R seed
    Mrow amp xi reserve eps b firstHeight budget key hz1 hz2 firstIndex units w deleted q fees Bsrc boxes
    rawRoot rawFamily chosen
  let receipt:=actual_native_root_source_receipt reflected second s R seed Mrow amp xi reserve eps b
    firstHeight budget key hz1 hz2 firstIndex units w deleted q fees children Bsrc boxes hBsrc hfirst sourceFacts hsources
  refine ⟨receipt,?_,?_⟩
  · exact actual_native_root_source_receipt_loss_room reflected second s R seed Mrow amp xi reserve eps b
      firstHeight budget key hz1 hz2 firstIndex units w deleted q fees children Bsrc boxes hBsrc hfirst sourceFacts hsources
  change (attach_native_root_low_rows reflected second s R seed C.globalBase Mrow amp xi reserve eps b
    firstHeight budget C.globalBase_gt_one key hz1 hz2 firstIndex units w deleted q fees children).value=_
  erw [attach_native_root_low_rows_value]
  apply Finset.sum_congr rfl
  intro r _
  rw [hvalue r]
  rfl
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_root_receipt_from_chosen_columns_with_loss
