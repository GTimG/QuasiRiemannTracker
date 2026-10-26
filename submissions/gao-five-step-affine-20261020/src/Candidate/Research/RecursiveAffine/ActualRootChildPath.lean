/- The literal bare-root LOW attachment retains the actual child NodeOutput.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualChildOutputRebase
import Candidate.Research.RecursiveAffine.RootForestReceipt
import Candidate.Research.RecursiveAffine.RootTraceTransport
import Candidate.Research.RecursiveAffine.NativeLowHistoryCode
import Candidate.Research.RecursiveAffine.NativeForestAttach

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1100000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153RegionalLow Cycle153SourceReturn Cycle153JointCount
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open Cycle63Moment Cycle63InitialMass
variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=alpha) M H}

namespace NodeOutput

/-- Rebase the actual first inner output to the original base and unit one.
The bare root is not represented by a fictitious ReachableNode. -/
def globalTraced {child : ReachableNode C (0:Fin 4)}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes) :
    TracedSuffixFamily (hH:=hH) child C.globalBase 1 :=
  TracedSuffixFamily.rebasePower C.globalBase_gt_one child.unit_pos child.unit_le_one (by norm_num)
    (by rw [Real.rpow_one]) (by ring)
    (TracedSuffixFamily.transportBase child.localBase_eq ⟨out.family,out.path⟩)

theorem globalTraced_value {child : ReachableNode C (0:Fin 4)}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes) :
    out.globalTraced.family.value=out.family.value := by
  unfold globalTraced
  rw [TracedSuffixFamily.rebasePower_value,TracedSuffixFamily.transportBase_value]

def globalFamilyAtRoot {child : ReachableNode C (0:Fin 4)}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (v : O) (hv : child.presentation.mult=v) :
    SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz v :=
  suffixFamilyRootEq hv out.globalTraced.family

theorem globalFamilyAtRoot_value {child : ReachableNode C (0:Fin 4)}
    {constant eps Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant eps Bsrc control degree boxes)
    (v : O) (hv : child.presentation.mult=v) :
    (out.globalFamilyAtRoot v hv).value=out.family.value := out.globalTraced_value

end NodeOutput

private def rootFamilyEqPrefix {eta : Character} {Z B T : ℝ} {v : O}
    {F G : SuffixFamily (hH:=hH) 0 4 eta Z B T v} (h : F=G)
    (d : SuffixDepth 4) (p : F.Prefix d) : G.Prefix d := h ▸ p

private theorem rootFamilyEqPrefix_fields {eta : Character} {Z B T : ℝ} {v : O}
    {F G : SuffixFamily (hH:=hH) 0 4 eta Z B T v} (h : F=G)
    (d : SuffixDepth 4) (p : F.Prefix d) :
    F.multiplier d p=G.multiplier d (rootFamilyEqPrefix h d p) ∧
      HEq (F.part d p) (G.part d (rootFamilyEqPrefix h d p)) ∧
      F.weight d p=G.weight d (rootFamilyEqPrefix h d p) ∧
      F.historyMissing d p=G.historyMissing d (rootFamilyEqPrefix h d p) := by
  cases h
  exact ⟨rfl,HEq.rfl,rfl,rfl⟩

private def rootEdgeReindex {x : Fin 14→ℝ} {m A l m' A' l' : ℝ}
    (E : RootTraceEdge (C:=C) x m A l) (hm : m'=m) (hA : A'=A) (hl : l'=l) :
    RootTraceEdge (C:=C) x m' A' l' where
  node:=E.node
  unit_eq:=E.unit_eq
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
  root_scale:=E.root_scale
  root_length:=E.root_length
  relative_scale:=by rw [hm,hl];exact E.relative_scale
  length_step:=by rw [hA];exact E.length_step
  capacity:=by rw [hA];exact E.capacity
  junction_model:=E.junction_model
  deletion_model:=E.deletion_model
  missing_model:=E.missing_model
  reduction_model:=E.reduction_model
  amplifierError:=E.amplifierError
  amplifierError_nonneg:=E.amplifierError_nonneg
  fineAmplifierError:=E.fineAmplifierError
  fineScalePad:=E.fineScalePad
  fineCapacityPad:=E.fineCapacityPad
  amplifier_model:=E.amplifier_model

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

/-- The actual LOW-only root Σ carrier receives the SAME rebased child
payload and genuine first edge. Future geometry is transported by the true
child prefix receipt; the raw root coefficient and missing radical are
inserted exactly once. Root marked HIGH remains a separate source. -/
def actual_root_child_path_from_output
    (units : FirstSourceLabel→O) (w : alpha→ℝ) (deleted : Rows→Finset alpha) (q : ℝ) (fees : Rows→ℝ)
    (children : (r : Rows)→SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz
      (Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1))
    (r : Rows) (child : ReachableNode C (0:Fin 4))
    (hroot : child.presentation.mult=Cycle63Moment.childMultiplier (!reflected) 1 units (rowKey r).1)
    {constant epsChild Bsrc : ℝ} {control : Finset (ℕ×ℕ)} {degree : ℕ} {boxes : ℕ→Finset (Fin 4→ℤ)}
    (out : NodeOutput hH child constant epsChild Bsrc control degree boxes)
    (hfamily : children r=out.globalFamilyAtRoot _ hroot)
    (edge : RootTraceEdge (C:=C) child.coordinates
      (child.unit*child.state.rowWidth)
      (child.unit*Real.logb child.localBase (volume (child.input hH)))
      (Real.logb C.globalBase ((Ideal.span {child.presentation.mult}).absNorm:ℝ)))
    (hraw : C.globalBase^(Mrow+actualHighCoordinates reflected (!reflected) second (first r.val.1)
      (rowKey r).1.2.1.1 (rowKey r).1.2.1.2 (rowKey r).1.2.2
      C.globalBase Mrow (Real.logb C.globalBase (volume s)) amp xi reserve eps 0+
        q*(∑i∈deleted r,w i)+fees r)=C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
          edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount))
    (hmissing : edge.node.coordinate 1=
      Real.logb C.globalBase ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ))
    (d : SuffixDepth 4) (p : (children r).Prefix d) :
    RootNativePath (attach_native_root_low_rows reflected second s R seed C.globalBase Mrow amp xi reserve eps b
      firstHeight budget C.globalBase_gt_one key hz1 hz2 firstIndex units w deleted q fees children) d ⟨r,p⟩ := by
  let Fc:=out.globalTraced
  let pc : Fc.family.Prefix d:=rootFamilyEqPrefix hfamily d p
  let trace:=Fc.path d pc
  have fields:=rootFamilyEqPrefix_fields hfamily d p
  have hpreserve : ∀i,prefixCoordinate 1 i→trace.coordinates i=child.coordinates i := trace.prefix_preserved
  let Efinal:=edge.transportFinal hpreserve
  let E:=rootEdgeReindex Efinal trace.root_scale trace.root_length trace.root_prefix
  refine { child:=child,childFamily:=Fc.family,childPrefix:=pc,trace:=trace,edge:=E
           multiplier:=fields.1,part:=fields.2.1,weight:=?_,missing:=?_ }
  · exact congrArg₂ (fun a b : ℝ=>a*b) hraw fields.2.2.1
  · exact congrArg₂ (fun a b : ℝ=>a+b) hmissing.symm fields.2.2.2

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.NodeOutput.globalFamilyAtRoot_value
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_child_path_from_output
