/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.PrimitiveStageSchedule
import Candidate.Research.RecursiveAffine.MarkedRebasedSchedule
import Candidate.Research.RecursiveAffine.RootLedgerBinding
import Candidate.Cycle63.Physical.InitialMass.CommonMeshMask

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153SourceSchedule
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open HeckeFamily Filter Set
open Cycle63InitialMass Cycle153Reachable
open Cycle153.RegionalSchedule Cycle63MarkedPlain

/-- The native primitive loss is independent of ambient cardinality,
original ray data, fixed seed character and the moving physical source. -/
def nativeMu : ℝ := primitiveError/128

theorem nativeMu_pos : 0<nativeMu := div_pos primitiveError_pos (by norm_num)

/-- The OLD epsilon is positive for every requested final epsilon. The
same smaller loss can serve every finite stage, and is paid by its native
LOW reserve before any child base is selected. -/
def oldLoss (eps : ℝ) : ℝ := min (eps/64) (nativeMu/1024)

theorem oldLoss_pos {eps : ℝ} (heps : 0<eps) : 0<oldLoss eps := by
  unfold oldLoss
  exact lt_min (by positivity) (div_pos nativeMu_pos (by norm_num))

theorem oldLoss_bounds (eps : ℝ) : oldLoss eps≤eps/64 ∧ oldLoss eps≤nativeMu/1024 :=
  ⟨min_le_left _ _,min_le_right _ _⟩

/-- This mesh is chosen before N and before every fixed/moving source.
Mask48 pays AtState's 28+20 mask; mask20 pays its original OLD moment;
the marked mesh pays the genuine 31-fold marked support gate. -/
def localSlotMesh (eps : ℝ) : ℝ :=
  min (1/(gridSize:ℝ))
    (min (Cycle25.Energy.commonMesh 2 48 1 (nativeMu/8))
      (min (Cycle25.Energy.commonMesh 1 20 1 (oldLoss eps/2))
        (markedGeometryMesh (nativeMu/8))))

def originalSlotMesh (eps : ℝ) : ℝ := (1/50:ℝ)*localSlotMesh eps

theorem localSlotMesh_pos {eps : ℝ} (heps : 0<eps) : 0<localSlotMesh eps := by
  have hg : (0:ℝ)<gridSize := by exact_mod_cast gridSize_pos
  unfold localSlotMesh
  exact lt_min (by positivity)
    (lt_min (Cycle25.Energy.commonMesh_pos 2 48 1 (nativeMu/8)
      (by norm_num) (by norm_num) (div_pos nativeMu_pos (by norm_num)))
      (lt_min (Cycle25.Energy.commonMesh_pos 1 20 1 (oldLoss eps/2)
        (by norm_num) (by norm_num) (div_pos (oldLoss_pos heps) (by norm_num)))
        (marked_geometry_mesh_gates (nativeMu/8) (div_pos nativeMu_pos (by norm_num))).1))

theorem originalSlotMesh_pos {eps : ℝ} (heps : 0<eps) : 0<originalSlotMesh eps :=
  mul_pos (by norm_num) (localSlotMesh_pos heps)

theorem localSlotMesh_gates {eps : ℝ} (_heps : 0<eps) :
    localSlotMesh eps≤1/(gridSize:ℝ) ∧ localSlotMesh eps≤nativeMu/8 ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 48 1 (nativeMu/8) ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 1 20 1 (oldLoss eps/2) ∧
    31*localSlotMesh eps≤ markedRawMesh*markedCoreMin := by
  have hgrid : localSlotMesh eps≤1/(gridSize:ℝ) := min_le_left _ _
  have hcommon : localSlotMesh eps≤Cycle25.Energy.commonMesh 2 48 1 (nativeMu/8) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hold : localSlotMesh eps≤Cycle25.Energy.commonMesh 1 20 1 (oldLoss eps/2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmarked : localSlotMesh eps≤ markedGeometryMesh (nativeMu/8) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm := marked_geometry_mesh_gates (nativeMu/8) (div_pos nativeMu_pos (by norm_num))
  exact ⟨hgrid,hmarked.trans hm.2.1,hcommon,hold,
    (mul_le_mul_of_nonneg_left hmarked (by norm_num : (0:ℝ)≤31)).trans hm.2.2⟩

/-- Native reserve information already gives an amplifier floor uniformly
over every rounded cell; no positive infimum over moving positions is
assumed. -/
theorem native_reserve_lt_half_amplifier [Cycle63.AffineLedger] :
    Cycle63.AffineLedger.lowReserve<Cycle63.AffineLedger.amplifierFloor/2 := by
  have hb : Cycle63.AffineLedger.firstCellTop≤Cycle63.AffineLedger.firstCellTop ∧
      Cycle63.AffineLedger.firstCellTop≤Cycle63.AffineLedger.slotTop :=
    ⟨le_rfl,Cycle63.AffineLedger.firstCellTop_le_slotTop⟩
  have hg := Cycle63.AffineLedger.g_pos hb
  have h := Cycle63.AffineLedger.lowReserve_le_errorReserves.1.trans
    (Cycle63.AffineLedger.first_error_reserve hb)
  have ha := Cycle63.AffineLedger.amplifierFloor_pos
  have hp := Cycle63.AffineLedger.primeFraction_lt_one
  change Cycle63.AffineLedger.lowReserve<
    Cycle63.AffineLedger.amp Cycle63.AffineLedger.firstCellTop/2
  change 0<Cycle63.AffineLedger.amp Cycle63.AffineLedger.firstCellTop at ha
  nlinarith only [h,hg,ha,hp]

/-- All literal AtState/HIGH mesh gates hold at any of the fixed native
ledgers whose loss unit is nativeMu. The bound is independent of N. -/
theorem local_native_mesh_gates [Cycle63.AffineLedger] {eps Bmask : ℝ}
    (heps : 0<eps) (hB0 : 0≤Bmask) (hB20 : Bmask≤20)
    (hreserve : 128*nativeMu≤Cycle63.AffineLedger.lowReserve) :
    localSlotMesh eps<Cycle63.AffineLedger.amplifierFloor/2 ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 (28+Bmask) 1 (nativeMu/8) ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 2 28 1 (nativeMu/8) ∧
    localSlotMesh eps≤Cycle25.Energy.commonMesh 1 Bmask 1 (oldLoss eps/2) := by
  have hm := localSlotMesh_gates heps
  have hle : localSlotMesh eps≤Cycle63.AffineLedger.lowReserve := by
    have hp := nativeMu_pos
    linarith only [hm.2.1,hreserve,hp]
  refine ⟨hle.trans_lt native_reserve_lt_half_amplifier,?_,?_,?_⟩
  · exact hm.2.2.1.trans (Cycle25.Energy.commonMesh_anti_mask 2 1 (nativeMu/8)
      (by norm_num) (B₁:=28+Bmask) (B₂:=48) (by linarith) (by linarith) (div_pos nativeMu_pos (by norm_num)))
  · exact hm.2.2.1.trans (Cycle25.Energy.commonMesh_anti_mask 2 1 (nativeMu/8)
      (by norm_num) (B₁:=28) (B₂:=48) (by norm_num) (by norm_num) (div_pos nativeMu_pos (by norm_num)))
  · exact hm.2.2.2.1.trans (Cycle25.Energy.commonMesh_anti_mask 1 1 (oldLoss eps/2)
      (by norm_num) (B₁:=Bmask) (B₂:=20) hB0 hB20 (div_pos (oldLoss_pos heps) (by norm_num)))

/-- Original widths fit the SAME local mesh after every actual rebase
U≥1/50. No N-dependent slot restriction is introduced by the schedule. -/
theorem rebased_original_weight {eps U w : ℝ} (heps : 0<eps)
    (hU : (1/50:ℝ)≤U) (hw : w≤originalSlotMesh eps) :
    w/U≤localSlotMesh eps := by
  have hu : 0<U := by linarith
  rw [div_le_iff₀ hu]
  have hm := (localSlotMesh_pos heps).le
  exact hw.trans (by unfold originalSlotMesh; nlinarith only [hU,hm])

/-- The native reserve pays the entire next-node OLD epsilon, including
when the actual normalized child unit varies. -/
theorem backward_old_loss_paid [Cycle63.AffineLedger] {eps u : ℝ}
    (heps : 0<eps) (_hu : 0≤u) (hu1 : u≤1)
    (hreserve : 128*nativeMu≤Cycle63.AffineLedger.lowReserve) :
    u*oldLoss eps≤Cycle63.AffineLedger.lowReserve/131072 := by
  have hmul := mul_le_mul_of_nonneg_right hu1 (oldLoss_pos heps).le
  have hb := (oldLoss_bounds eps).2
  nlinarith only [hmul,hb,hreserve]
end
end OAI.SevenEighths.Cycle153SourceSchedule
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.native_reserve_lt_half_amplifier
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.local_native_mesh_gates
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.rebased_original_weight
#print axioms OAI.SevenEighths.Cycle153SourceSchedule.backward_old_loss_paid
