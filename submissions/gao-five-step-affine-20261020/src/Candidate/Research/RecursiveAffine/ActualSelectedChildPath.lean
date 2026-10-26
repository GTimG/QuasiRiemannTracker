/- The genuine child NodeOutput and physical source edge give the exact selected-row path.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedReceipt
import Candidate.Research.RecursiveAffine.ActualChildOutputRebase

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
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


private def familyEqPrefix {start count : ℕ} {eta : Character} {Z B T : ℝ} {v : O}
    {F G : SuffixFamily (hH:=hH) start count eta Z B T v} (h : F=G)
    (d : SuffixDepth count) (p : F.Prefix d) : G.Prefix d := h ▸ p

private theorem familyEqPrefix_fields {start count : ℕ} {eta : Character} {Z B T : ℝ} {v : O}
    {F G : SuffixFamily (hH:=hH) start count eta Z B T v} (h : F=G)
    (d : SuffixDepth count) (p : F.Prefix d) :
    F.multiplier d p=G.multiplier d (familyEqPrefix h d p) ∧
      HEq (F.part d p) (G.part d (familyEqPrefix h d p)) ∧
      F.weight d p=G.weight d (familyEqPrefix h d p) ∧
      F.historyMissing d p=G.historyMissing d (familyEqPrefix h d p) := by
  cases h
  exact ⟨rfl,HEq.rfl,rfl,rfl⟩

private def edgeReindex {x : Fin 14→ℝ} {m A l m' A' l' : ℝ}
    (E : NativeTraceEdge (hH:=hH) parent x m A l)
    (hm : m'=m) (hA : A'=A) (hl : l'=l) : NativeTraceEdge (hH:=hH) parent x m' A' l' where
  node:=E.node
  fee:=E.fee
  sourceGates:=E.sourceGates
  fineSource:=E.fineSource
  fineFee:=E.fineFee
  remainingFee:=E.remainingFee
  V:=E.V
  Red:=E.Red
  residualF:=E.residualF
  residualF_nonneg:=E.residualF_nonneg
  capacityPad:=E.capacityPad
  scalePad:=E.scalePad
  amplifierError:=E.amplifierError
  amplifierError_nonneg:=E.amplifierError_nonneg
  fineAmplifierError:=E.fineAmplifierError
  fineScalePad:=E.fineScalePad
  fineCapacityPad:=E.fineCapacityPad
  root_scale:=E.root_scale
  root_length:=E.root_length
  relative_scale:=by rw [hm,hl];exact E.relative_scale
  length_step:=by rw [hA];exact E.length_step
  capacity:=by rw [hA];exact E.capacity
  prefix_preserved:=E.prefix_preserved
  length_model:=E.length_model
  unit_model:=E.unit_model
  junction_model:=E.junction_model
  deletion_model:=E.deletion_model
  missing_model:=E.missing_model
  reduction_model:=E.reduction_model
  amplifier_model:=E.amplifier_model

/-- Bind the literal continuing branch to its SAME strict-IH output.
The root equality is the actual native continuation prefix equality; the
family equality identifies the guarded source branch, not a new count or
energy estimate. The genuine physical edge is transported only through
prefix preservation to the child's final future coordinates. -/
def actual_selected_child_path_from_output
    (units : FirstSourceLabel→O)
    (children : (r : Rows)→SuffixFamily (hH:=hH) (j.val+1) (4-(j.val+1)) C.etaSeed
      parent.localBase C.Bnorm C.Tz (Cycle63Moment.childMultiplier (!reflected)
        parent.presentation.mult units (rowKey r).1))
    (rawEdge missing : Rows→ℝ) (r : Rows)
    (child : ReachableNode C (nextInner j hj)) (hunit : child.unit≤parent.unit)
    (hroot : child.presentation.mult=Cycle63Moment.childMultiplier (!reflected)
      parent.presentation.mult units (rowKey r).1)
    {constant epsChild Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ}
    {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant epsChild Bsrc control degree boxes)
    (hfamily : children r=out.parentFamilyAtRoot parent hunit _ hroot)
    (edge : NativeTraceEdge (hH:=hH) parent child.coordinates
      (child.unit*child.state.rowWidth)
      (child.unit*Real.logb child.localBase (volume (child.input hH)))
      (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ)))
    (hraw : rawEdge r=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
      edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount))
    (hmissing : edge.node.coordinate 1=parent.unit*missing r)
    (d : SuffixDepth (4-(j.val+1))) (p : (children r).Prefix d) :
    NativeSelectedChildPath parent hj reflected s R seed Mrow amp xi reserve b firstHeight budget key
      hz1 hz2 firstIndex units children rawEdge missing r d p := by
  let Fc:=out.parentTraced parent hunit
  let pc : Fc.family.Prefix d:=familyEqPrefix hfamily d p
  let trace:=Fc.path d pc
  have fields:=familyEqPrefix_fields hfamily d p
  have hpreserve : ∀i,prefixCoordinate (j.val+2) i→trace.coordinates i=child.coordinates i := by
    intro i hi
    apply trace.prefix_preserved i
    simpa only [nextInner] using hi
  let Efinal:=edge.transportFinal trace.coordinates hpreserve
  let E:=edgeReindex parent Efinal trace.root_scale trace.root_length trace.root_prefix
  refine {
    child:=child,family:=Fc.family,childPrefix:=pc,trace:=trace
    multiplier:=fields.1
    part:=fields.2.1
    weight:=fields.2.2.1
    historyMissing:=fields.2.2.2
    edge:=E
    rawWeight:=hraw
    rawMissing:=hmissing }

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_selected_child_path_from_output
