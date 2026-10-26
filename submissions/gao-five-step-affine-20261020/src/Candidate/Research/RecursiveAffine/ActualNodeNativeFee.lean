/- Exact native source fees in the actual node and original physical unit.
Copyright (c) 2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextFee
import Candidate.Research.RecursiveAffine.SourceContextThreshold
import Candidate.Research.RecursiveAffine.NativeNodeStep

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open Cycle63InitialMass Cycle153SourceSchedule Cycle153.RegionalSchedule

/-- Exact change of physical unit: all additive prices and original
widths scale; the density junction remains the same. -/
def NativePathFee.scale (fee : NativePathFee)(u : ℝ)(hu : 0 ≤ u) : NativePathFee where
  driverDelta:=u*fee.driverDelta
  driverError:=u*fee.driverError
  coefficientError:=u*fee.coefficientError
  shellCost:=u*fee.shellCost
  sourcePad:=u*fee.sourcePad
  slotLoss:=u*fee.slotLoss
  junction:=fee.junction
  actualDeletion:=u*fee.actualDeletion
  nativeTargetDeletion:=u*fee.nativeTargetDeletion
  modelDeletion:=u*fee.modelDeletion
  primeMesh:=u*fee.primeMesh
  primeMesh_nonneg:=mul_nonneg hu fee.primeMesh_nonneg
  deletion_upper:=by nlinarith only [mul_le_mul_of_nonneg_left fee.deletion_upper hu]
  roundingError:=u*fee.roundingError
  roundingError_nonneg:=mul_nonneg hu fee.roundingError_nonneg
  target_eq:=by rw [fee.target_eq];ring

theorem NativePathFee.amount_scale (fee : NativePathFee)(u : ℝ)(hu : 0 ≤ u) :
    (fee.scale u hu).amount=u*fee.amount :=by
  dsimp only [NativePathFee.amount,NativePathFee.scale]
  ring

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- The literal finite geometry pad used by nativeNodeStepValues. It
contains the actual current cardinality and the same source endpoints. -/
def actualNodeLocalSourcePad (N : ReachableNode C j) : ℝ :=
  2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+
    Real.logb N.localBase (max 1 (N.input hH).b₁*max 1 (N.input hH).b₂)

/-- The actual fee uses physical sourcecap130 and the actual detector
cardinality. The larger postShellCost/ambient nativeSlotLoss are used
only to prove an upper budget, never as replacements in the raw edge. -/
def actualNodeLocalFee (N : ReachableNode C j)(eps : ℝ)(budget : ℕ)
    (Rdel : Finset N.slots)
    (hdeleted : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+C.slotMesh) : NativePathFee where
  driverDelta:=nativeDriverRate budget
  driverError:=oldLoss eps
  coefficientError:=postDictionaryRate C.Bnorm budget
  shellCost:=130*postDictionaryRate C.Bnorm budget
  sourcePad:=actualNodeLocalSourcePad (hH:=hH) N
  slotLoss:=2*nativeDriverRate budget*31*(Fintype.card N.slots:ℝ)
  junction:=(innerStage j.val).q
  actualDeletion:=∑i∈Rdel,C.originalWeight i/N.unit
  nativeTargetDeletion:=nodeDetectorDeletion N
  modelDeletion:=pathDeletion j.val N.coordinates/N.unit
  primeMesh:=C.slotMesh
  primeMesh_nonneg:=C.slotMesh_pos.le
  deletion_upper:=hdeleted
  roundingError:=nodeDetectorDeletion N-pathDeletion j.val N.coordinates/N.unit
  roundingError_nonneg:=by have hh:=(nodeDetectorDeletion_bounds N).1;norm_num only at hh;linarith only [hh]
  target_eq:=by ring

def actualNodeGlobalFee (N : ReachableNode C j)(eps : ℝ)(budget : ℕ)
    (Rdel : Finset N.slots)
    (hdeleted : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+C.slotMesh) : NativePathFee :=
  (actualNodeLocalFee (hH:=hH) N eps budget Rdel hdeleted).scale N.unit N.unit_pos.le

theorem actual_node_fee_model (N : ReachableNode C j)(eps : ℝ)(budget : ℕ)
    (Rdel : Finset N.slots)
    (hdeleted : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+C.slotMesh) :
    (actualNodeGlobalFee (hH:=hH) N eps budget Rdel hdeleted).modelDeletion=pathDeletion j.val N.coordinates :=by
  change N.unit*(pathDeletion j.val N.coordinates/N.unit)=_
  field_simp [N.unit_pos.ne']

/-- The exact raw selected-row fee, including actual-minus-model deletion
and the true slot mesh, acquires precisely the current source unit. -/
theorem actual_node_fee_amount (N : ReachableNode C j)(eps : ℝ)(budget : ℕ)
    (Rdel : Finset N.slots)
    (hdeleted : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+C.slotMesh) :
    (actualNodeGlobalFee (hH:=hH) N eps budget Rdel hdeleted).amount=
      N.unit*(3*nativeDriverRate budget+oldLoss eps+postDictionaryRate C.Bnorm budget+
        130*postDictionaryRate C.Bnorm budget+actualNodeLocalSourcePad (hH:=hH) N+
        2*nativeDriverRate budget*31*(Fintype.card N.slots:ℝ)+
        (innerStage j.val).q*((∑i∈Rdel,C.originalWeight i/N.unit)-pathDeletion j.val N.coordinates/N.unit+C.slotMesh)) :=by
  rw [actualNodeGlobalFee,NativePathFee.amount_scale]
  rfl

/-- Native source geometry proves the actual finite pad and the scheduled
fee, uniformly before all moving nodes and literal detector deletions.
No pad, fine fee or remaining-weight inequality is a premise. -/
theorem eventually_actual_node_fee_budget (eps : ℝ)(heps : 0<eps)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(j : Fin 4)(N : ReachableNode C j),C.globalBase=Z→
      C.gridDenominator=gridSize→C.slotMesh ≤ localSlotMesh eps→Fintype.card N.slots ≤ budget→
    ∀(Rdel : Finset N.slots)
      (hdeleted : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+C.slotMesh),
      (actualNodeGlobalFee (hH:=hH) N eps budget Rdel hdeleted).amount ≤ 1/(10:ℝ)^15 :=by
  filter_upwards [eventually_actual_native_pad budget] with Z hz
  refine ⟨hz.1,?_⟩
  intro C j N hbase hgrid hmesh hcard Rdel hdeleted
  have hb1 : (N.input hH).b₁=(9/4:ℝ) :=rfl
  have hb2 : (N.input hH).b₂=(9/4:ℝ) :=rfl
  have hpadFull:=hz.2 N.unit N.unit_floor (Fintype.card N.slots) hcard (9/4) (N.input hH).b₁ (N.input hH).b₂
    (by norm_num) le_rfl hb1.le hb2.le
  rw [←hbase,←N.localBase_eq] at hpadFull
  have hlog128 : 0 ≤ Real.logb N.localBase 128:=Real.logb_nonneg N.localBase_gt_one (by norm_num)
  have hg : 0 ≤ 252/(gridSize:ℝ) :=by positivity
  have hpad : actualNodeLocalSourcePad (hH:=hH) N ≤ 1/(10:ℝ)^20 :=by
    dsimp only [actualNodeLocalSourcePad]
    linarith only [hpadFull,hlog128,hg]
  have hmodel : pathDeletion j.val N.coordinates/N.unit ≤ nodeDetectorDeletion N :=by
    have hh:=(nodeDetectorDeletion_bounds N).1;linarith only [hh]
  have hdeleted' : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+localSlotMesh eps :=by
    linarith only [hdeleted,hmesh]
  have hround : nodeDetectorDeletion N-pathDeletion j.val N.coordinates/N.unit ≤
      2200/(gridSize:ℝ)+1/(10:ℝ)^20 :=by
    have hh:=(nodeDetectorDeletion_bounds N).2
    rw [hgrid] at hh
    norm_num [gridSize] at hh ⊢
    linarith only [hh]
  have hq : 0 ≤ (innerStage j.val).q ∧ (innerStage j.val).q ≤ 1 :=by
    have hh:=(innerStage j.val).q_le_price
    have hhh:=(innerStage j.val).price_le_one
    exact ⟨(innerStage j.val).q_pos.le,hh.trans hhh⟩
  let larger:=scheduledNativeFee eps heps budget C.Bnorm (pathDeletion j.val N.coordinates/N.unit)
    (nodeDetectorDeletion N) (∑i∈Rdel,C.originalWeight i/N.unit) (innerStage j.val).q
    (actualNodeLocalSourcePad (hH:=hH) N) hmodel hdeleted'
  have hbudget:=scheduledNativeFee_budget heps C.normCap_nonneg budget _ _ _ _ _ hmodel hdeleted' hq.1 hq.2 hpad hround
  have hrate:=postDictionaryRate_budgets C.normCap_nonneg budget
  have hB : (130:ℝ) ≤ C.Bnorm:=by linarith only [C.normCap_large]
  have hshell : 130*postDictionaryRate C.Bnorm budget ≤ postShellCost C.Bnorm budget :=by
    dsimp only [postShellCost]
    have hN : (0:ℝ) ≤ budget:=Nat.cast_nonneg budget
    nlinarith only [hrate.1,mul_nonneg hN hrate.1.le,mul_nonneg (sub_nonneg.mpr hB) hrate.1.le]
  have hslot : 2*nativeDriverRate budget*31*(Fintype.card N.slots:ℝ) ≤ nativeSlotLoss budget :=by
    have hc : (Fintype.card N.slots:ℝ) ≤ budget:=by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_left hc (by have hp:=(nativeDriverRate_budgets budget).1;positivity)
  have hcompare : (actualNodeLocalFee (hH:=hH) N eps budget Rdel hdeleted).amount ≤ larger.amount :=by
    dsimp only [actualNodeLocalFee,larger,scheduledNativeFee,NativePathFee.amount]
    have hm:=mul_le_mul_of_nonneg_left hmesh hq.1
    linarith only [hshell,hslot,hm]
  have hlocal : (actualNodeLocalFee (hH:=hH) N eps budget Rdel hdeleted).amount ≤ 1/(10:ℝ)^15 :=
    hcompare.trans hbudget
  rw [actualNodeGlobalFee,NativePathFee.amount_scale]
  have hm:=mul_le_mul_of_nonneg_left hlocal N.unit_pos.le
  nlinarith only [hm,N.unit_le_one]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.eventually_actual_node_fee_budget
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_node_fee_amount
