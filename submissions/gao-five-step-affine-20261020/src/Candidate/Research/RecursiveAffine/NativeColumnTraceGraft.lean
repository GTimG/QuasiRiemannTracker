/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedSourceReceipt
import Candidate.Research.RecursiveAffine.NativeColumnTrace
import Candidate.Research.RecursiveAffine.NativeChosenSourceEdge

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
open Cycle153ActualColumn
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

/-- Arithmetic metadata extracted from the SAME chosen native Columns
continuation. No new IH output is selected: output is supplied by the
actual source trace. Its analytic family value is retained exactly. -/
structure ChosenInnerColumn (units : FirstSourceLabel→O)
    (rawEdge missing : Rows→ℝ)(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz (rawRoot r))(r : Rows) where
  child : ReachableNode C (nextInner j hj)
  unit : child.unit ≤ parent.unit
  root : child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) parent.presentation.mult units (rowKey r).1
  constant : ℝ
  epsilon : ℝ
  control : Finset (ℕ×ℕ)
  degree : ℕ
  output : NodeOutput hH child constant epsilon Bsrc control degree (fun k=>boxes (k+1))
  edge : NativeTraceEdge (hH:=hH) parent child.coordinates
    (child.unit*child.state.rowWidth)
    (child.unit*Real.logb child.localBase (volume (child.input hH)))
    (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ))
  rawWeight : rawEdge r=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
    edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)
  rawMissing : edge.node.coordinate 1=parent.unit*missing r
  value : (rawFamily r).value=output.family.value

/-- Extract the arithmetic choice from the actual named native Column
trace. The existing output is preserved literally; the only callback is
the genuine source arithmetic edge constructor at that exact child. It
contains no energy, returned-count or future-output premise. -/
theorem actual_native_column_trace_chosen
    (units : FirstSourceLabel→O)(rawEdge missing : Rows→ℝ)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz (rawRoot r))(r : Rows)
    {Daughter : Type}(admitted : Daughter→Prop)(sourceRow : Daughter→O→ℂ)
    (J : Daughter→Finset parent.slots)(w : parent.slots→ℝ)(del mesh : ℝ)
    (continues : Daughter→Finset parent.slots→Prop)
    (child : ∀d,admitted d→∀z,sourceRow d z≠0→∀Rd : Finset parent.slots,
      Rd⊆J d→(∑i∈Rd,w i)≤del+mesh→(Rd=J d ∨ del≤∑i∈Rd,w i)→
      continues d Rd→ReachableNode C (nextInner j hj))
    (constant epsilon : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)
    (daughter : Daughter)(Rd : Finset parent.slots)
    (trace : NativeColumnOutputTrace admitted sourceRow J w del mesh continues child
      constant epsilon Bsrc control degree (fun k=>boxes (k+1)) daughter Rd (rawFamily r))
    (arithmetic : ∀(hn : admitted daughter)(z : O)(hne : sourceRow daughter z≠0)
      (hR : Rd⊆J daughter)(hsum : (∑i∈Rd,w i)≤del+mesh)
      (hcover : Rd=J daughter ∨ del≤∑i∈Rd,w i)(hc : continues daughter Rd),
      let kept:=child daughter hn z hne Rd hR hsum hcover hc
      ∃hu : kept.unit ≤ parent.unit,
      ∃hroot : kept.presentation.mult=Cycle63Moment.childMultiplier (!reflected)
        parent.presentation.mult units (rowKey r).1,
      ∃edge : NativeTraceEdge (hH:=hH) parent kept.coordinates
        (kept.unit*kept.state.rowWidth)
        (kept.unit*Real.logb kept.localBase (volume (kept.input hH)))
        (Real.logb C.globalBase ((Ideal.span {kept.presentation.mult}).absNorm:ℝ)),
        rawEdge r=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
          edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount) ∧
        edge.node.coordinate 1=parent.unit*missing r) :
    rawFamily r=emptyReturnedForest ∨ Nonempty (ChosenInnerColumn parent hj reflected
      s R seed Mrow amp xi reserve b firstHeight budget key hz1 hz2 firstIndex units rawEdge missing
      Bsrc boxes rawRoot rawFamily r) := by
  by_cases hz : rawFamily r=emptyReturnedForest
  · exact Or.inl hz
  · obtain ⟨hn,z,hne,hR,hsum,hcover,hc,out,hvalue⟩:=trace.live hz
    obtain ⟨hu,hroot,edge,hraw,hmissing⟩:=arithmetic hn z hne hR hsum hcover hc
    exact Or.inr ⟨{
      child:=child daughter hn z hne Rd hR hsum hcover hc,
      unit:=hu,root:=hroot,constant:=constant,epsilon:=epsilon,control:=control,degree:=degree,
      output:=out,edge:=edge,rawWeight:=hraw,rawMissing:=hmissing,value:=hvalue }⟩

/-- Replace each analytic native Column family by the SAME chosen
NodeOutput rebased and rerooted at its literal first source multiplier.
The whole actual selected-row carrier is retained, including zero
branches. The resulting source receipts and exact value equality let the
analytic OLD/common estimate and arithmetic count use one family. -/
theorem actual_columns_to_inner_source_choices
    (units : FirstSourceLabel→O)(rawEdge missing : Rows→ℝ)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz (rawRoot r))
    (chosen : ∀r,rawFamily r=emptyReturnedForest ∨ Nonempty (ChosenInnerColumn parent hj reflected
      s R seed Mrow amp xi reserve b firstHeight budget key hz1 hz2 firstIndex units rawEdge missing
      Bsrc boxes rawRoot rawFamily r)) :
    ∃children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) parent.presentation.mult units (rowKey r).1),
    (∀r,(children r).value=(rawFamily r).value) ∧
    ∀r,children r=emptyReturnedForest ∨ Nonempty (NativeSelectedChildSource parent hj reflected
      s R seed Mrow amp xi reserve b firstHeight budget key hz1 hz2 firstIndex units children
      rawEdge missing Bsrc boxes r) := by
  let data := fun (r : Rows)(hn : rawFamily r≠emptyReturnedForest)=>
    Classical.choice ((chosen r).resolve_left hn)
  let children := fun r=>if hz : rawFamily r=emptyReturnedForest then emptyReturnedForest else
    (data r hz).output.parentFamilyAtRoot parent (data r hz).unit _ (data r hz).root
  refine ⟨children,?_,?_⟩
  · intro r
    by_cases hz : rawFamily r=emptyReturnedForest
    · have hc : children r=emptyReturnedForest :=by simp only [children,dif_pos hz]
      calc
        (children r).value=0 :=by rw [hc];exact emptyReturnedForest_value
        _=(rawFamily r).value :=by rw [hz];exact emptyReturnedForest_value.symm
    · simp only [children,dif_neg hz]
      exact ((data r hz).output.parentFamilyAtRoot_value parent (data r hz).unit _ (data r hz).root).trans
        (data r hz).value.symm
  · intro r
    by_cases hz : rawFamily r=emptyReturnedForest
    · exact Or.inl (by simp only [children,dif_pos hz];rfl)
    · let d:=data r hz
      refine Or.inr ⟨{
        child:=d.child,unit:=d.unit,root:=d.root,constant:=d.constant,epsilon:=d.epsilon,
        control:=d.control,degree:=d.degree,output:=d.output,family:=?_,edge:=d.edge,
        rawWeight:=d.rawWeight,rawMissing:=d.rawMissing }⟩
      simp only [children,dif_neg hz]
      rfl

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_columns_to_inner_source_choices

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_column_trace_chosen
