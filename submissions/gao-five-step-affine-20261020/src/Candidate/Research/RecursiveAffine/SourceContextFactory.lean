/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextMesh

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open HeckeFamily Filter Set
open CenteredMomentNaturalFixedRaySource
open Cycle63InitialMass Cycle153Reachable Cycle153.RegionalSchedule

/-- The returned norm cap pays all four possible historical source caps
in addition to the native fixed-prefix allowance. It is not the physical
sourcecap130 used by the native source theorem. -/
def returnedNormCap (Bsrc : ℝ) : ℝ := 4*Bsrc+200130

def physicalSourceCap : ℝ := 130

theorem returnedNormCap_large {Bsrc : ℝ} (hBsrc : 0≤Bsrc) :
    (200130:ℝ)≤returnedNormCap Bsrc := by unfold returnedNormCap;linarith

theorem historical_source_budget {Bsrc : ℝ} (hBsrc : 0≤Bsrc) {n : ℕ} (hn : n≤4) :
    (n:ℝ)*Bsrc≤returnedNormCap Bsrc-200130 := by
  have hc : (n:ℝ)≤4 := by exact_mod_cast hn
  have h:=mul_le_mul_of_nonneg_right hc hBsrc
  simpa only [returnedNormCap,add_sub_cancel_right] using h

/-- The actual initial source is fixed at W, etaSeed and Q, while all
moving weighted-ray inputs obey the already chosen mesh. The constructor
contains no energy or moment estimate. In particular mesh does not depend
on the ambient cardinality, Bsrc, the fixed seed, or moving profiles. -/
def sourceContext {α : Type} [Fintype α] [DecidableEq α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (eps : ℝ) (heps : 0<eps)
    (Bsrc Kclass : ℝ) (hBsrc : 0≤Bsrc) (hKclass : 0≤Kclass)
    (etaSeed : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQsmall : internalQ Q etaSeed≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (Z : ℝ) (hZ : 1<Z) (Tz : ℝ)
    (theta : α→RayQuotient.Characters M H) (weight sigma frequency : α→ℝ)
    (hweight : ∀i,0≤weight i) (hmesh : ∀i,weight i≤originalSlotMesh eps)
    (hsigma : ∀i,sigma i∈Icc (33/50:ℝ) (33/50)) : SourceContext (α:=α) M H where
  globalBase:=Z
  globalBase_gt_one:=hZ
  etaSeed:=etaSeed
  Q:=Q
  Q_le_M:=hQM
  fixed_small:=hQsmall
  W:=W
  W_smooth:=hW
  W_support:=hWs
  theta:=theta
  originalWeight:=weight
  originalWeight_nonneg:=hweight
  sigma:=sigma
  sigma_fixed:=hsigma
  frequency:=frequency
  gridDenominator:=gridSize
  grid_positive:=gridSize_pos
  slotMesh:=localSlotMesh eps
  slotMesh_pos:=localSlotMesh_pos heps
  slotMesh_grid:=(localSlotMesh_gates heps).1
  originalWeight_mesh:=hmesh
  Bnorm:=returnedNormCap Bsrc
  normCap_nonneg:=le_trans (by norm_num) (returnedNormCap_large hBsrc)
  normCap_large:=returnedNormCap_large hBsrc
  highClassCap:=Kclass
  highClassCap_nonneg:=hKclass
  Tz:=Tz

/-- Every terminal prefix consumes at most four source caps. This is the
literal budget needed by the noncircular whole-forest coarse attainer. -/
theorem suffix_source_budget {Bsrc : ℝ} (hBsrc : 0≤Bsrc)
    (j : Fin 4) (d : SuffixDepth (4-j.val)) :
    (suffixOffset (4-j.val) d:ℝ)*Bsrc≤returnedNormCap Bsrc := by
  have hn:=suffixOffset_lt (4-j.val) d
  have hb:=historical_source_budget hBsrc (n:=suffixOffset (4-j.val) d) (by omega)
  linarith only [hb]

/-- The fixed root ledger has the same tiny actual loss unit as the
four rounded inner ledgers. Only q/price/intercept enter this identity. -/
theorem root_native_mu :
    @geometryLossUnit Cycle153.Root.rootLedger 1 primitiveError=nativeMu := by
  have hr : @Cycle63.AffineLedger.lowReserve Cycle153.Root.rootLedger =
      Cycle63.Optimization.lowReserveAt Cycle153.MarkedRootPrice.price
        Cycle153.MarkedRootPrice.intercept Cycle153.MarkedRootPrice.q := rfl
  simp only [geometryLossUnit,hr,mul_one]
  norm_num [nativeMu,primitiveError,Cycle153.MarkedRootPrice.price,
    Cycle153.MarkedRootPrice.intercept,Cycle153.MarkedRootPrice.q,Cycle153.FixedStages.stage0,
    Cycle63.Optimization.lowReserveAt,Cycle63.Optimization.lowReserveWeight,
    Cycle63.Optimization.allowanceUnit]

theorem root_native_reserve :
    128*nativeMu≤@Cycle63.AffineLedger.lowReserve Cycle153.Root.rootLedger := by
  have h:=(@geometry_loss_unit_reserve Cycle153.Root.rootLedger 1 primitiveError 1 le_rfl).2
  rw [root_native_mu] at h
  norm_num only [one_mul] at h
  linarith only [h]

theorem regional_native_reserve (j : Fin 5)
    (i : Cycle153.RegionalIndex (stage j) gridSize) :
    128*nativeMu≤@Cycle63.AffineLedger.lowReserve (Cycle153.regionalFamily (stage j) gridSize i) := by
  have h:=(@geometry_loss_unit_reserve (Cycle153.regionalFamily (stage j) gridSize i)
    1 primitiveError 1 le_rfl).2
  rw [primitive_native_mu j i] at h
  change 64*nativeMu≤1*(_/2) at h
  linarith only [h]

/-- The schedule supplies the actual root/common/OLD/marked/grid gates
before any ambient N or moving source is selected. -/
theorem root_source_mesh_gates {eps : ℝ} (heps : 0<eps) :
    localSlotMesh eps<@Cycle63.AffineLedger.amplifierFloor Cycle153.Root.rootLedger/2 ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 48 1 (nativeMu/8) ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 28 1 (nativeMu/8) ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 1 20 1 (oldLoss eps/2) := by
  simpa only [show (28:ℝ)+20=48 by norm_num] using
    (@local_native_mesh_gates Cycle153.Root.rootLedger eps 20 heps (by norm_num)
      le_rfl root_native_reserve)

/-- All rounded inner ledgers have the same source mesh gates. The
coordinate grid affects no original prime width restriction. -/
theorem regional_source_mesh_gates {eps : ℝ} (heps : 0<eps) (j : Fin 5)
    (i : Cycle153.RegionalIndex (stage j) gridSize) :
    localSlotMesh eps<@Cycle63.AffineLedger.amplifierFloor
      (Cycle153.regionalFamily (stage j) gridSize i)/2 ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 48 1 (nativeMu/8) ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 28 1 (nativeMu/8) ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 1 20 1 (oldLoss eps/2) := by
  simpa only [show (28:ℝ)+20=48 by norm_num] using
    (@local_native_mesh_gates (Cycle153.regionalFamily (stage j) gridSize i) eps 20 heps
      (by norm_num) le_rfl (regional_native_reserve j i))
end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.sourceContext
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.suffix_source_budget
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.root_native_mu
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.root_source_mesh_gates
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.regional_source_mesh_gates
