/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSourceReceipt
import Candidate.Research.RecursiveAffine.ActualChildHistory
import Candidate.Research.RecursiveAffine.ActualChildTerminalFacts

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
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

theorem actual_native_root_source_receipt_loss_room
    (units : FirstSourceLabel→O)(w : alpha→ℝ)(deleted : Rows→Finset alpha)(q : ℝ)(fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1))
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(hBsrc : 0 ≤ Bsrc)
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : Rows,DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
      C.globalBase Bsrc (boxes 0) ((),rowKey r))
    (sources : ∀r,children r=emptyReturnedForest ∨ Nonempty (NativeRootSelectedSource reflected second
      s R seed Mrow amp xi reserve eps b firstHeight budget key hz1 hz2 firstIndex
      units w deleted q fees children Bsrc boxes r)) :
    ∀d p,((actual_native_root_source_receipt reflected second s R seed Mrow amp xi reserve eps b firstHeight
      budget key hz1 hz2 firstIndex units w deleted q fees children Bsrc boxes hBsrc hfirst sourceFacts sources).family.part d p).loss
      ≤ 5/1000000000000 :=by
  intro d p
  rcases p with ⟨r,pc⟩
  change ((children r).part d pc).loss≤_
  rcases sources r with hz | hs
  · have hp : (children r).Prefix d→False:=by rw [hz];exact fun p=>nomatch p
    exact False.elim (hp pc)
  · let data:=(Classical.choice hs).data
    have hf:=data.output.globalTerminalFacts _ data.root
    rw [←data.family] at hf
    exact (hf.loss d pc).trans (by norm_num [terminalLossCap])

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_root_source_receipt_loss_room
