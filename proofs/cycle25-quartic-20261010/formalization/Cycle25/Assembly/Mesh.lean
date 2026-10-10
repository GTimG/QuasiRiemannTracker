import Cycle25.Energy.Endpoint

noncomputable section
namespace Cycle25

/-- One mesh for both the physical numerator and the marked detector family. -/
def sourceMesh (t : ℝ) : ℝ := Energy.commonMesh 2 0 1 (t/4)

theorem sourceMesh_pos {t : ℝ} (ht : 0 < t) : 0 < sourceMesh t := by
  exact Energy.commonMesh_pos 2 0 1 (t/4) (by norm_num) (by norm_num) (by positivity)

end Cycle25
