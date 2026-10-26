/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedReceiptBuild
import Candidate.Research.RecursiveAffine.ActualChildHistory
import Candidate.Research.RecursiveAffine.ActualSelectedChildPath
import Candidate.Research.RecursiveAffine.ActualChildTerminalFacts

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

/-- One actual nonterminal selected source keeps its genuine deeper
NodeOutput and SAME native first edge. The zero source instead has a
literal empty carrier. No independently postulated path or count appears. -/
structure NativeSelectedChildSource
    (units : FirstSourceLabel→O)
    (children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed parent.localBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) parent.presentation.mult units (rowKey r).1))
    (rawEdge missing : Rows→ℝ)(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(r : Rows) where
  child : ReachableNode C (nextInner j hj)
  unit : child.unit ≤ parent.unit
  root : child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) parent.presentation.mult units (rowKey r).1
  constant : ℝ
  epsilon : ℝ
  control : Finset (ℕ×ℕ)
  degree : ℕ
  output : NodeOutput hH child constant epsilon Bsrc control degree (fun k=>boxes (k+1))
  family : children r=output.parentFamilyAtRoot parent unit _ root
  edge : NativeTraceEdge (hH:=hH) parent child.coordinates
    (child.unit*child.state.rowWidth)
    (child.unit*Real.logb child.localBase (volume (child.input hH)))
    (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ))
  rawWeight : rawEdge r=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
    edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)
  rawMissing : edge.node.coordinate 1=parent.unit*missing r

/-- Construct the actual selected inner forest from physical source
choices. Histories, source caps, losses, class licences and full native
paths are all derived from the SAME deeper output, before any current
node energy or weighted count is asserted. -/
def actual_native_inner_source_receipt
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz parent.presentation.mult)
    (w : parent.slots→ℝ)(deleted : Rows→Finset parent.slots)(q : ℝ)(fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed parent.localBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) parent.presentation.mult units (rowKey r).1))
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
    (sources : ∀r,children r=emptyReturnedForest ∨ Nonempty (NativeSelectedChildSource parent hj
      reflected s R seed Mrow amp xi reserve b firstHeight budget key hz1 hz2 firstIndex units children
      (fun r=>parent.localBase^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
        (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2 parent.localBase Mrow
        (Real.logb parent.localBase (volume s)) amp xi reserve eps 0+q*(∑i∈deleted r,w i)+fees r))
      (fun r=>Real.logb parent.localBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ))
      Bsrc boxes r)) : NativeNodeForestReceipt hH parent Bsrc boxes := by
  refine actual_native_selected_receipt parent hj reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex units own w deleted q fees children Bsrc boxes hfirst sourceFacts
    ?_ hm hA ampError hAmp0 hAmpFine hAmp ownLoss
    (actual_own_terminal_source_caps parent own hm hA ha) ownClass ?_ ?_ ?_ ?_
  · intro r
    apply Classical.choice
    rcases sources r with hz | hs
    · rw [hz];exact ⟨OrientedFamilyHistory.empty _ _ _⟩
    · let data:=Classical.choice hs
      have hh:=data.output.parentHistory hBsrc parent data.unit _ data.root
      rw [data.family]
      exact ⟨hh⟩
  · intro r d p
    rcases sources r with hz | hs
    · have hp : (children r).Prefix d→False := by rw [hz];exact fun p=>nomatch p
      exact False.elim (hp p)
    · let data:=Classical.choice hs
      have hf:=data.output.parentTerminalFacts parent data.unit _ data.root
      rw [←data.family] at hf
      exact (hf.loss d p).trans (terminalLossCap_mono (j:=j) (k:=nextInner j hj) (by simp only [nextInner];omega))
  · intro r d p
    rcases sources r with hz | hs
    · have hp : (children r).Prefix d→False := by rw [hz];exact fun p=>nomatch p
      exact False.elim (hp p)
    · let data:=Classical.choice hs
      have hf:=data.output.parentTerminalFacts parent data.unit _ data.root
      rw [←data.family] at hf
      exact hf.source d p
  · intro r d p b
    rcases sources r with hz | hs
    · have hp : (children r).Prefix d→False := by rw [hz];exact fun p=>nomatch p
      exact False.elim (hp p)
    · let data:=Classical.choice hs
      have hf:=data.output.parentTerminalFacts parent data.unit _ data.root
      rw [←data.family] at hf
      exact hf.classCap d p b
  · intro r d p
    apply Classical.choice
    rcases sources r with hz | hs
    · have hp : (children r).Prefix d→False := by rw [hz];exact fun p=>nomatch p
      exact False.elim (hp p)
    · let data:=Classical.choice hs
      exact ⟨actual_selected_child_path_from_output parent hj reflected s R seed Mrow amp xi reserve b
        firstHeight budget key hz1 hz2 firstIndex units children _ _ r data.child data.unit data.root
        data.output data.family data.edge data.rawWeight data.rawMissing d p⟩

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_inner_source_receipt
