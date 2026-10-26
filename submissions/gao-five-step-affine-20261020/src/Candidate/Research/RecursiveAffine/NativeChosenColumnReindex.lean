/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeColumnTraceGraft

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

/-- Reindex only the external analytic family functions after making the
ONE simultaneous actual source choice. The genuine child, output, edge
and raw payment remain identical. Only equalities at this same row are
used; no second output or family is chosen. -/
def ChosenInnerColumn.reindexAnalytic
    (units : FirstSourceLabel→O)(rawEdge missing : Rows→ℝ)
    (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))(rawRoot : Rows→O)
    (rawFamily : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz (rawRoot r))(r : Rows)
    (chosen : ChosenInnerColumn parent hj reflected s R seed Mrow amp xi reserve b firstHeight budget
      key hz1 hz2 firstIndex units rawEdge missing Bsrc boxes rawRoot rawFamily r)
    (newEdge newMissing : Rows→ℝ)(newRoot : Rows→O)
    (newFamily : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz (newRoot r))
    (hweight : newEdge r=rawEdge r)(hmissing : newMissing r=missing r)
    (hvalue : (newFamily r).value=(rawFamily r).value) :
    ChosenInnerColumn parent hj reflected s R seed Mrow amp xi reserve b firstHeight budget
      key hz1 hz2 firstIndex units newEdge newMissing Bsrc boxes newRoot newFamily r :=
  { child:=chosen.child
    unit:=chosen.unit
    root:=chosen.root
    constant:=chosen.constant
    epsilon:=chosen.epsilon
    control:=chosen.control
    degree:=chosen.degree
    output:=chosen.output
    edge:=chosen.edge
    rawWeight:=hweight.trans chosen.rawWeight
    rawMissing:=chosen.rawMissing.trans (congrArg (fun x=>parent.unit*x) hmissing).symm
    value:=hvalue.trans chosen.value }

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.ChosenInnerColumn.reindexAnalytic
