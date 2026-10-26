/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedSourceReceipt
import Candidate.Research.RecursiveAffine.ActualChildHistory
import Candidate.Research.RecursiveAffine.ActualSelectedChildPath
import Candidate.Research.RecursiveAffine.ActualChildTerminalFacts

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
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

attribute [local irreducible] geometryFirstLabel actualHighCoordinates

/- One genuine native shell fee fits the actual fixed-depth loss schedule. -/
theorem actual_native_inner_source_receipt_loss_room
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
      Bsrc boxes r))
    (shift : ℝ)(hshift : shift ≤ 1/1000000000000)
    (ownRoom : own.loss+shift ≤ terminalLossCap j) :
    ∀d p,((actual_native_inner_source_receipt parent hj reflected second s R seed Mrow amp xi reserve eps b firstHeight
      budget key hz1 hz2 firstIndex units own w deleted q fees children Bsrc boxes hBsrc hfirst sourceFacts
      hm hA ha ampError hAmp0 hAmpFine hAmp ownLoss ownClass sources).family.part d p).loss+shift ≤ terminalLossCap j :=by
  have hstep : terminalLossCap (nextInner j hj)+shift ≤ terminalLossCap j :=by
    unfold terminalLossCap nextInner
    push_cast
    linarith only [hshift]
  intro d p
  change ((actualNativeSuffixRows parent hj reflected second s R seed Mrow amp xi reserve eps b firstHeight
    budget key hz1 hz2 firstIndex units own w deleted q fees children).part d p).loss+shift ≤ terminalLossCap j
  fin_cases j
  all_goals try (norm_num at hj)
  all_goals
    cases d with
    | none=>exact ownRoom
    | some dc=>
      rcases p with ⟨r,pc⟩
      change ((children r).part dc pc).loss+shift ≤ _
      rcases sources r with hz | hs
      · have hp : (children r).Prefix dc→False :=by rw [hz];exact fun p=>nomatch p
        exact False.elim (hp pc)
      · let data:=Classical.choice hs
        have hf:=data.output.parentTerminalFacts parent data.unit _ data.root
        rw [←data.family] at hf
        have hh := hf.loss dc pc
        linarith only [hh,hstep]

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_inner_source_receipt_loss_room
