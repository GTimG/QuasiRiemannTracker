/- The SAME native Columns output supplies the root returned forest.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSourceReceipt
import Candidate.Research.RecursiveAffine.NativeColumnTrace
import Candidate.Research.RecursiveAffine.NativeRootChosenSourceEdge

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
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

/-- Source metadata of the SAME live Columns selection. Its output is
never selected a second time, and its family value remains literal. -/
structure ChosenRootColumn (units : FirstSourceLabel→O)(w : alpha→ℝ)
    (deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz (rawRoot r))
    (r : Rows) where
  child : ReachableNode C 0
  root : child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1
  constant : ℝ
  epsilon : ℝ
  control : Finset (ℕ×ℕ)
  degree : ℕ
  output : NodeOutput hH child constant epsilon Bsrc control degree (fun k=>boxes (k+1))
  edge : RootTraceEdge (C:=C) child.coordinates
    (child.unit*child.state.rowWidth)
    (child.unit*Real.logb child.localBase (volume (child.input hH)))
    (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ))
  rawWeight : C.globalBase^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 C.globalBase Mrow
      (Real.logb C.globalBase (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r)=
    C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
      edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)
  rawMissing : edge.node.coordinate 1=
    Real.logb C.globalBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)
  value : (rawFamily r).value=output.family.value

/-- Replace an analytic Column family by the SAME chosen out rebased to
the global root and rerooted by its true arithmetic multiplier. This
changes no scalar value, source choice, terminal part or raw coefficient. -/
theorem actual_columns_to_root_source_choices
    (units : FirstSourceLabel→O)(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz (rawRoot r))
    (chosen : ∀r,rawFamily r=emptyReturnedForest ∨ Nonempty (ChosenRootColumn reflected second
      s R seed Mrow amp xi reserve eps b firstHeight budget key hz1 hz2 firstIndex
      units w deleted q fees Bsrc boxes rawRoot rawFamily r)) :
    ∃children : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1),
    (∀r,(children r).value=(rawFamily r).value) ∧
    ∀r,children r=emptyReturnedForest ∨ Nonempty (NativeRootSelectedSource reflected second
      s R seed Mrow amp xi reserve eps b firstHeight budget key hz1 hz2 firstIndex
      units w deleted q fees children Bsrc boxes r) :=by
  let data:=fun (r : Rows)(hn : rawFamily r≠emptyReturnedForest)=>
    Classical.choice ((chosen r).resolve_left hn)
  let children:=fun r=>if hz : rawFamily r=emptyReturnedForest then emptyReturnedForest else
    (data r hz).output.globalFamilyAtRoot _ (data r hz).root
  refine ⟨children,?_,?_⟩
  · intro r
    by_cases hz : rawFamily r=emptyReturnedForest
    · have hc : children r=emptyReturnedForest:=by simp only [children,dif_pos hz]
      calc
        (children r).value=0:=by rw [hc];exact emptyReturnedForest_value
        _=(rawFamily r).value:=by rw [hz];exact emptyReturnedForest_value.symm
    · simp only [children,dif_neg hz]
      exact ((data r hz).output.globalFamilyAtRoot_value _ (data r hz).root).trans (data r hz).value.symm
  · intro r
    by_cases hz : rawFamily r=emptyReturnedForest
    · exact Or.inl (by simp only [children,dif_pos hz])
    · let d:=data r hz
      refine Or.inr ⟨{
        data:={
          child:=d.child
          root:=d.root
          constant:=d.constant
          epsilon:=d.epsilon
          Bsrc:=Bsrc
          control:=d.control
          degree:=d.degree
          boxes:=fun k=>boxes (k+1)
          output:=d.output
          family:=?_
          edge:=d.edge
          rawWeight:=d.rawWeight
          rawMissing:=d.rawMissing }
        sourceCap:=rfl
        sourceBoxes:=rfl }⟩
      simp only [children,dif_neg hz]
      rfl
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_columns_to_root_source_choices
