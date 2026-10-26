/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualRootChildPath
import Candidate.Research.RecursiveAffine.NativeRootSelectedChronology

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization Cycle153SourceReturn Cycle153Reachable Cycle153JointCount

variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}
variable (reflected second : Bool) (s : Input alpha) (R seed : Ideal O)
variable (Mrow amp xi reserve eps b firstHeight : ℝ) (budget : ℕ)
variable (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (C.globalBase^Mrow)
  C.globalBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
local notation "Rows"=>NativeLowRows reflected s R seed C.globalBase Mrow amp xi reserve b
  firstHeight budget C.globalBase_gt_one key hz1 hz2 firstIndex
local notation "first"=>fun l=>geometryFirstLabel s R seed (C.globalBase^Mrow) C.globalBase xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
local notation "rowKey"=>nativeLowHistoryCode reflected s R seed C.globalBase Mrow amp xi reserve b
  firstHeight budget C.globalBase_gt_one key hz1 hz2 firstIndex

/-- Actual source provenance for one continuing root row. The output is
from the first genuine inner node, not from a fictitious width-one root.
The family equality retains that SAME output after the literal rebase;
the first physical edge has its exact native coefficient and missing radical. -/
structure NativeRootSelectedChild
    (units : FirstSourceLabel→O)(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1)) (r : Rows) where
  child : ReachableNode C (0:Fin 4)
  root : child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1
  constant : ℝ
  epsilon : ℝ
  Bsrc : ℝ
  control : Finset (ℕ×ℕ)
  degree : ℕ
  boxes : ℕ→Finset (Fin 4→ℤ)
  output : NodeOutput hH child constant epsilon Bsrc control degree boxes
  family : children r=output.globalFamilyAtRoot _ root
  edge : RootTraceEdge (C:=C) child.coordinates
    (child.unit*child.state.rowWidth)
    (child.unit*Real.logb child.localBase (volume (child.input hH)))
    (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ))
  rawWeight : C.globalBase^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
    (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2
    C.globalBase Mrow (Real.logb C.globalBase (volume s)) amp xi reserve eps 0+
      q*(∑i∈deleted r,w i)+fees r)=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
        edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)
  rawMissing : edge.node.coordinate 1=
    Real.logb C.globalBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ)

/-- Assemble the full root LOW receipt on the actual native sum of row
carriers. A zero row contributes its literal empty carrier; every other
row is the same genuine inner NodeOutput selected by the source operator.
The native key injection constructs chronology, and the first root edge
is attached once. No root energy, weighted count or class payment is an input. -/
def actual_native_root_selected_receipt
    (units : FirstSourceLabel→O)(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1))
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
      C.globalBase Bsrc (boxes 0) ((),rowKey r))
    (histories : ∀r,OrientedFamilyHistory (children r) (suffixOffset 4) Bsrc (fun k=>boxes (k+1)))
    (sources : ∀r,children r=emptyReturnedForest ∨ Nonempty (NativeRootSelectedChild reflected second
      s R seed Mrow amp xi reserve eps b firstHeight budget key hz1 hz2 firstIndex
      units w deleted q fees children r))
    (childrenLoss : ∀r d p,((children r).part d p).loss ≤ 6/1000000000000)
    (childrenSource : ∀r d p,TerminalSourceCaps ((children r).part d p).scale
      ((children r).part d p).length ((children r).part d p).amp
      (Real.logb C.globalBase ((Ideal.span {(children r).multiplier d p}).absNorm:ℝ)))
    (childrenClass : ∀r d p b,(Fintype.card (((children r).part d p).record b).Class:ℝ) ≤ C.highClassCap) :
    NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes := by
  let F : RootLowFamily (hH:=hH) C:=attach_native_root_low_rows reflected second s R seed C.globalBase Mrow amp
    xi reserve eps b firstHeight budget C.globalBase_gt_one key hz1 hz2 firstIndex units w deleted q fees children
  refine { family:=F,chronology:=?_,path:=?_,terminalLoss:=?_,terminalSource:=?_,classCap:=?_ }
  · exact actual_native_root_low_oriented_history reflected s R seed C.globalBase Mrow amp xi reserve b
      firstHeight budget C.globalBase_gt_one key hz1 hz2 firstIndex second eps units w deleted q fees children
      hfirst Bsrc boxes sourceFacts (suffixOffset 4) (fun d=>by have hd:=suffixOffset_lt 4 d;omega) histories
  · intro d p
    rcases p with ⟨r,pc⟩
    apply Classical.choice
    rcases sources r with hzero | hsource
    · have hp : (children r).Prefix d→False := by rw [hzero];exact fun p=>nomatch p
      exact False.elim (hp pc)
    · let data:=Classical.choice hsource
      exact ⟨actual_root_child_path_from_output reflected second s R seed Mrow amp xi reserve eps b firstHeight
        budget key hz1 hz2 firstIndex units w deleted q fees children r data.child data.root data.output
        data.family data.edge data.rawWeight data.rawMissing d pc⟩
  · intro d p;exact childrenLoss p.1 d p.2
  · intro d p;exact childrenSource p.1 d p.2
  · intro d p b;exact childrenClass p.1 d p.2 b

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_root_selected_receipt
