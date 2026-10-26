/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.AnalyticPrimitive
import Candidate.Research.RecursiveAffine.RegionalAtState
import Candidate.Research.RecursiveAffine.SourceContextMesh

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153AnalyticPrimitive
noncomputable section
open scoped Classical HeckeNotation ContDiff
open Set HeckeFamily Cycle63InitialMass Cycle153RegionalState

/-- This is the requested exponent of the actual OLD moment, distinct
from analyticError which fixes the physical source loss unit. -/
def nodeError (eps : ℝ) : ℝ := min (eps/64) (mu/1024)

theorem nodeError_pos {eps : ℝ} (heps : 0<eps) : 0<nodeError eps := by
  unfold nodeError
  exact lt_min (by positivity) (div_pos mu_pos (by norm_num))

theorem nodeError_budgets (eps : ℝ) : nodeError eps≤ eps/64 ∧ nodeError eps≤ mu/1024 :=
  ⟨min_le_left _ _,min_le_right _ _⟩

/-- Actual native AtState accepts these two errors independently. It
constructs the OLD exponent 1+nodeError through its source reduction,
comparison, Mellin and parent-mass proof; it does not assume a smaller
child moment in order to obtain that exponent. -/
theorem actual_small_error_at_state
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc 1 2)
    (hbetaLo : 51/100≤ HeckeZeroSupremum.beta) (hbetaHi : HeckeZeroSupremum.beta≤ 7/8)
    (g : GeometryAffineLowSchedule) (bPhi Bmask mesh eps : ℝ) :
    RegionalAtStateStatement (α:=alpha) M H hH W hW hWs hbetaLo hbetaHi
      g analyticError bPhi Bmask mesh (nodeError eps) :=
  actual_regional_affine_at_state M H hH W hW hWs hbetaLo hbetaHi
    g analyticError bPhi Bmask mesh (nodeError eps)

/-- The original prime mesh can still be chosen before the ambient slot
cardinality. It pays actual OLD comparison, LOW common and marked gates;
changing the analytic loss does not coarsen the coordinate grid. -/
def localMesh (eps : ℝ) : ℝ :=
  min (1/(Cycle153.RegionalSchedule.gridSize:ℝ))
    (min (Cycle25.Energy.commonMesh 2 48 1 (mu/8))
      (min (Cycle25.Energy.commonMesh 1 20 1 (nodeError eps/2))
        (Cycle63MarkedPlain.markedGeometryMesh (mu/8))))

theorem localMesh_pos {eps : ℝ} (heps : 0<eps) : 0<localMesh eps := by
  have hg : (0:ℝ)< Cycle153.RegionalSchedule.gridSize := by
    exact_mod_cast Cycle153.RegionalSchedule.gridSize_pos
  unfold localMesh
  exact lt_min (by positivity)
    (lt_min (Cycle25.Energy.commonMesh_pos 2 48 1 (mu/8)
      (by norm_num) (by norm_num) (div_pos mu_pos (by norm_num)))
      (lt_min (Cycle25.Energy.commonMesh_pos 1 20 1 (nodeError eps/2)
        (by norm_num) (by norm_num) (div_pos (nodeError_pos heps) (by norm_num)))
        (Cycle63MarkedPlain.marked_geometry_mesh_gates (mu/8) (div_pos mu_pos (by norm_num))).1))

theorem localMesh_gates {eps : ℝ} (heps : 0<eps) :
    localMesh eps≤ 1/(Cycle153.RegionalSchedule.gridSize:ℝ) ∧
      localMesh eps≤ mu/8 ∧
      localMesh eps≤ Cycle25.Energy.commonMesh 2 48 1 (mu/8) ∧
      localMesh eps≤ Cycle25.Energy.commonMesh 1 20 1 (nodeError eps/2) ∧
      31*localMesh eps≤ Cycle63MarkedPlain.markedRawMesh*Cycle63MarkedPlain.markedCoreMin := by
  have hgrid : localMesh eps≤ 1/(Cycle153.RegionalSchedule.gridSize:ℝ) := min_le_left _ _
  have hcommon : localMesh eps≤ Cycle25.Energy.commonMesh 2 48 1 (mu/8) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hold : localMesh eps≤ Cycle25.Energy.commonMesh 1 20 1 (nodeError eps/2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmarked : localMesh eps≤ Cycle63MarkedPlain.markedGeometryMesh (mu/8) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm:=Cycle63MarkedPlain.marked_geometry_mesh_gates (mu/8) (div_pos mu_pos (by norm_num))
  exact ⟨hgrid,hmarked.trans hm.2.1,hcommon,hold,
    (mul_le_mul_of_nonneg_left hmarked (by norm_num : (0:ℝ)≤ 31)).trans hm.2.2⟩

/-- The same native amplifier floor gate is met at the actual ledgers. -/
theorem actual_amplifier_mesh [Cycle63.AffineLedger] {eps : ℝ}
    (heps : 0<eps) (hmu : geometryLossUnit 1 analyticError=mu) :
    localMesh eps< Cycle63.AffineLedger.amplifierFloor/2 := by
  have hr:=actual_native_reserve hmu
  have hm:=(localMesh_gates heps).2.1
  have h : localMesh eps≤ Cycle63.AffineLedger.lowReserve := by
    nlinarith only [hr,hm,mu_pos]
  exact h.trans_lt Cycle153SourceSchedule.native_reserve_lt_half_amplifier

end
end OAI.SevenEighths.Cycle153AnalyticPrimitive
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.actual_small_error_at_state
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.localMesh_gates
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.actual_amplifier_mesh
