/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedChronology
import Candidate.Research.RecursiveAffine.NativeWholeNodeForest
import Candidate.Research.RecursiveAffine.ActualTraceTransport
import Candidate.Research.RecursiveAffine.PhysicalStepCoordinates

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
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
variable {C : SourceContext (α:=alpha) M H} {j : Fin 4}
variable (parent : ReachableNode C j) (hj : j.val < 3)
variable (reflected second : Bool) (s : Input parent.slots) (R seed : Ideal O)
variable (Mrow amp xi reserve eps b firstHeight : ℝ) (budget : ℕ)
variable (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
variable (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (parent.localBase^Mrow)
  parent.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans parent.localBase_gt_one) _) key)

local notation "Rows" => NativeLowRows reflected s R seed parent.localBase Mrow amp xi reserve b
  firstHeight budget parent.localBase_gt_one key hz1 hz2 firstIndex
local notation "first" => fun l=>geometryFirstLabel s R seed (parent.localBase^Mrow) parent.localBase xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans parent.localBase_gt_one) _) key (firstIndex l).1.val
local notation "rowKey" => nativeLowHistoryCode reflected s R seed parent.localBase Mrow amp xi reserve b
  firstHeight budget parent.localBase_gt_one key hz1 hz2 firstIndex
local notation "childRoot" => fun r : Rows=>Cycle63Moment.childMultiplier (!reflected)
  parent.presentation.mult units (rowKey r).1

/-- The actual native attachment has exactly the finite remaining-depth
carrier of its parent. This only resolves the recursive dictionary
indices; every source row, part, weight and missing radical is literal. -/
def actualNativeSuffixRows
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz parent.presentation.mult)
    (w : parent.slots→ℝ) (deleted : Rows→Finset parent.slots) (q : ℝ) (fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed
      parent.localBase C.Bnorm C.Tz (Cycle63Moment.childMultiplier (!reflected)
        parent.presentation.mult units (rowKey r).1)) : parent.Family hH := by
  change SuffixFamily (hH:=hH) j.val (4-j.val) C.etaSeed parent.localBase C.Bnorm C.Tz
    parent.presentation.mult
  have hcount : 4-j.val=(4-(j.val+1))+1 := by omega
  rw [hcount]
  let A:=attach_native_low_rows reflected second s R seed parent.localBase Mrow amp xi reserve eps b
    firstHeight budget parent.localBase_gt_one key hz1 hz2 firstIndex units own w deleted q fees children
  exact { Prefix:=A.Prefix
          prefixFintype:=A.prefixFintype
          multiplier:=A.multiplier
          root_divides:=A.root_divides
          historyMissing:=A.historyMissing
          historyMissing_nonneg:=A.historyMissing_nonneg
          part:=fun d=>by
            cases d with
            | none=>exact A.part none
            | some d=>exact A.part (some d)
          weight:=A.weight
          weight_nonneg:=A.weight_nonneg }


/-- A selected continuing prefix retains the actual rebased child,
its SAME terminal record, and its actual first native edge. These are
source identities and source-gate receipts; no payment or energy claim
is stored. A terminal/OLD row has an empty carrier and needs no datum. -/
structure NativeSelectedChildPath
    (units : FirstSourceLabel→O)
    (children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed
      parent.localBase C.Bnorm C.Tz (Cycle63Moment.childMultiplier (!reflected)
        parent.presentation.mult units (rowKey r).1))
    (rawEdge missing : Rows→ℝ)
    (r : Rows) (d : SuffixDepth (4-(j.val+1))) (p : (children r).Prefix d) where
  child : ReachableNode C (nextInner j hj)
  family : SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed parent.localBase
    C.Bnorm C.Tz child.presentation.mult
  childPrefix : family.Prefix d
  trace : ActualPathTrace hH child parent.unit family d childPrefix
  multiplier : (children r).multiplier d p=family.multiplier d childPrefix
  part : HEq ((children r).part d p) (family.part d childPrefix)
  weight : (children r).weight d p=family.weight d childPrefix
  historyMissing : (children r).historyMissing d p=family.historyMissing d childPrefix
  edge : NativeTraceEdge (hH:=hH) parent trace.coordinates
    (trace.scale 0) (trace.volumeLength 0) (trace.prefixLog 0)
  rawWeight : rawEdge r=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
    edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)
  rawMissing : edge.node.coordinate 1=parent.unit*missing r

/-- Every coefficient of the native attachment appears once, with no
change of source key or class carrier while resolving depth dictionaries. -/
theorem actualNativeSuffixRows_value
    (units : FirstSourceLabel→O)
    (own : ReturnedPartAt M H hH (innerStage j.val).q (prefixDictionary (j.val+1))
      C.etaSeed parent.localBase C.Bnorm C.Tz parent.presentation.mult)
    (w : parent.slots→ℝ) (deleted : Rows→Finset parent.slots) (q : ℝ) (fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed
      parent.localBase C.Bnorm C.Tz (Cycle63Moment.childMultiplier (!reflected)
        parent.presentation.mult units (rowKey r).1)) :
    (actualNativeSuffixRows parent hj reflected second s R seed Mrow amp xi reserve eps b firstHeight
      budget key hz1 hz2 firstIndex units own w deleted q fees children).value=
      own.value+∑r : Rows,parent.localBase^(Mrow+
        actualHighCoordinates reflected (!reflected) second (first r.val.1)
          (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2
          parent.localBase Mrow (Real.logb parent.localBase (volume s)) amp xi reserve eps 0+
          q*(∑i∈deleted r,w i)+fees r)*(children r).value := by
  have hsame : (actualNativeSuffixRows parent hj reflected second s R seed Mrow amp xi reserve eps b firstHeight
      budget key hz1 hz2 firstIndex units own w deleted q fees children).value=
      (attach_native_low_rows reflected second s R seed parent.localBase Mrow amp xi reserve eps b firstHeight
        budget parent.localBase_gt_one key hz1 hz2 firstIndex units own w deleted q fees children).value := by
    fin_cases j
    all_goals try (norm_num at hj)
    all_goals
      unfold actualNativeSuffixRows DepthReturnedFamily.value
      apply Finset.sum_congr rfl
      intro d hd
      cases d <;> rfl
  rw [hsame]
  exact attach_native_low_rows_value reflected second s R seed parent.localBase Mrow amp xi reserve eps b firstHeight
    budget parent.localBase_gt_one key hz1 hz2 firstIndex units own w deleted q fees children


end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actualNativeSuffixRows_value
