/- Whole ROOT row families retain their actual one-column paid outputs.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootColumnPaidResult
import Candidate.Research.RecursiveAffine.NativeRootColumnChoices
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

private theorem coordinate_at_unit_one {Z : ℝ}(p : NativePaidPathNode Z)(hu : p.unit=1)(k : Fin 4) :
    p.coordinate k=actualHighCoordinates p.reflected (!p.reflected) p.second p.first p.C p.D p.inactive
      Z p.rowWidth p.length p.amp p.xi p.reserve p.eps k:=by
  dsimp only [NativePaidPathNode.coordinate]
  rw [hu,Real.rpow_one,one_mul]

/-- A pointwise actual source result becomes the literal whole-row
chosen-source interface. Every edge/output/family is copied from that
same result; no depth or component is maximized independently. -/
theorem actual_root_paid_rows_to_choices
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
    ∀r,(result r).family=emptyReturnedForest ∨
      Nonempty (ChosenRootColumn (C:=C) (hH:=hH) reflected second s 1 1 1 (rootSourceAmp C.originalWeight)
        (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8) epsRow (9/4) firstHeight
        (Fintype.card alpha) key hz1 hz2 firstIndex units C.originalWeight (fun rr=>(result rr).deleted)
        Coordinates.q0 (fun _=>massLoss+actualRootRemainingFeesAtMesh C s epsNode feeBudget mesh)
        Bsrc boxes rawRoot (fun rr=>(result rr).family) r) :=by
  intro Rows rowKey paid rawRoot hroot energy fixed old coefficient result r
  rcases (result r).choice with hz|⟨chosen,out,hdeleted,edge,hprefix,hnode,hfee,hraw,hmissing,hvalue⟩
  · exact Or.inl hz
  · refine Or.inr ⟨{
      child:=chosen,root:=hprefix.trans (hroot r),constant:=constant,epsilon:=epsilon,
      control:=control,degree:=degree,output:=out,edge:=edge,rawWeight:=?_,rawMissing:=?_,value:=hvalue }⟩
    · have hcoord : (paid r).coordinate 0=actualHighCoordinates reflected (!reflected) second
        (paid r).first (paid r).C (paid r).D (paid r).inactive C.globalBase 1
        (Real.logb C.globalBase (volume s)) (rootSourceAmp C.originalWeight)
        (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8) epsRow 0:=
        coordinate_at_unit_one (paid r) rfl 0
      have hscale : (paid r).scale=1:=by change (1:ℝ)*1=1;rw [one_mul]
      have hshift : (paid r).shiftedOutside=(paid r).coordinate 0+massLoss:=by
        change (paid r).coordinate 0+1*massLoss=_
        rw [one_mul]
      calc
        _=rootNativePaidCoefficient C s (paid r) epsNode feeBudget mesh (result r).deleted:=by
          change C.globalBase^(1+actualHighCoordinates reflected (!reflected) second
            (paid r).first (paid r).C (paid r).D (paid r).inactive C.globalBase 1
            (Real.logb C.globalBase (volume s)) (rootSourceAmp C.originalWeight)
            (Cycle153SourceSchedule.nativeMu/64) (Cycle153SourceSchedule.nativeMu/8) epsRow 0+
            Coordinates.q0*(∑i∈(result r).deleted,C.originalWeight i)+
            (massLoss+actualRootRemainingFeesAtMesh C s epsNode feeBudget mesh))=_
          unfold rootNativePaidCoefficient
          rw [hscale,hshift,hcoord]
          congr 1
          ring
        _=_:=hraw
    · calc
        edge.node.coordinate 1=(paid r).coordinate 1:=hmissing
        _=_:=by
          rw [coordinate_at_unit_one (paid r) rfl 1]
          rfl

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_root_paid_rows_to_choices
