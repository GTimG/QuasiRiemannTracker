/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RebasedStageSchedule
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule

set_option autoImplicit false
namespace Cycle153.RegionalSchedule
noncomputable section
open OAI.SevenEighths.Cycle63MarkedPlain

/-- The original slot mesh is fixed before every Fourier cardinality,
profile or density degree. The native marked cap is paid in local units. -/
def rootMarkedPrimeMesh (Umin μ : ℝ) : ℝ :=
  Umin*markedGeometryMesh (min (μ/8) (Cycle25.Energy.commonMesh 2 28 1 (μ/8)))

theorem rootMarkedPrimeMesh_pos {Umin μ : ℝ} (hUmin : 0< Umin) (hμ : 0<μ) :
    0< rootMarkedPrimeMesh Umin μ := by
  have hm : 0< min (μ/8) (Cycle25.Energy.commonMesh 2 28 1 (μ/8)) :=
    lt_min (by positivity) (Cycle25.Energy.commonMesh_pos 2 28 1 (μ/8)
      (by norm_num) (by norm_num) (by positivity))
  exact mul_pos hUmin (marked_geometry_mesh_gates _ hm).1

/-- The same original mesh supplies all three literal local source gates:
AtState's μ/8, the incumbent common mesh, and the marked detector's
31-fold support budget. No U-dependent mesh is chosen afterwards. -/
theorem rebased_marked_weight_gates {Umin μ U w : ℝ}
    (hUmin : 0< Umin) (hμ : 0<μ) (hU : Umin≤ U)
    (hw : w≤ rootMarkedPrimeMesh Umin μ) :
    w/U≤μ/8 ∧ w/U≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8) ∧
      31*(w/U)≤ markedRawMesh*markedCoreMin := by
  let localMesh := min (μ/8) (Cycle25.Energy.commonMesh 2 28 1 (μ/8))
  have hm : 0< localMesh := lt_min (by positivity)
    (Cycle25.Energy.commonMesh_pos 2 28 1 (μ/8)
      (by norm_num) (by norm_num) (by positivity))
  have hg := marked_geometry_mesh_gates localMesh hm
  have hu : 0< U := hUmin.trans_le hU
  have hlocal : w/U≤ markedGeometryMesh localMesh := by
    rw [div_le_iff₀ hu]
    change w≤ markedGeometryMesh localMesh*U
    exact hw.trans (by
      change Umin*markedGeometryMesh localMesh≤ markedGeometryMesh localMesh*U
      nlinarith [mul_le_mul_of_nonneg_right hU hg.1.le])
  have hp := hlocal.trans hg.2.1
  exact ⟨hp.trans (min_le_left _ _),hp.trans (min_le_right _ _),
    (mul_le_mul_of_nonneg_left hlocal (by norm_num : (0:ℝ)≤31)).trans hg.2.2⟩

end
end Cycle153.RegionalSchedule

#print axioms Cycle153.RegionalSchedule.rootMarkedPrimeMesh_pos
#print axioms Cycle153.RegionalSchedule.rebased_marked_weight_gates
