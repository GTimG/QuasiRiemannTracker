/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Cycle25.Energy.Endpoint
import Candidate.Cycle25.Assembly.Count.PlainInput
import Candidate.Cycle25.Assembly.Mesh
import Candidate.Cycle25.Assembly.Count.ActualMoments
import Candidate.Cycle63.Physical.InitialMass.MarkedParameters

/-! The slot mesh required by the detector affine moment at loss `ε`.
These are early copies of `geometryLossUnit 1`, `comparisonMesh 1 1` and
`geometryChosenMesh` (bundles B087, B138, B139); `Affine.Supply` proves the
copies equal to the originals. -/

set_option autoImplicit false

namespace DetectorAffine
noncomputable section

def meshLossUnit (ε : ℝ) : ℝ :=
  min (ε/128) (min ((7/30000000)*1/128) (min (1/128) (1/128)))

def meshCompare (ε : ℝ) : ℝ :=
  Cycle25.Energy.commonMesh (2*1+1) 0 ((2*1+1)+1/100+1) ((ε/2)/(4*((2*1+1)+2)))

def meshAnalytic (ε : ℝ) : ℝ :=
  let μ := meshLossUnit (ε/4)
  min (meshCompare (ε/4))
    (min (Cycle25.Energy.commonMesh 2 28 1 (μ/8))
      (min (μ/8) (1*(902420521/120632400000)/4)))/2

/-- Mesh cap for the detector slots: the affine moment then holds at loss `ε`. -/
def detectorMesh (ε : ℝ) : ℝ :=
  OAI.SevenEighths.Cycle63MarkedPlain.markedGeometryMesh
    (min (meshAnalytic ε) (meshCompare (ε/2)))

theorem meshLossUnit_pos {ε : ℝ} (hε : 0 < ε) : 0 < meshLossUnit ε := by
  unfold meshLossUnit; positivity

theorem meshCompare_pos {ε : ℝ} (hε : 0 < ε) : 0 < meshCompare ε := by
  unfold meshCompare
  exact Cycle25.Energy.commonMesh_pos _ _ _ _ (by norm_num) le_rfl (by positivity)

theorem meshAnalytic_pos {ε : ℝ} (hε : 0 < ε) : 0 < meshAnalytic ε := by
  unfold meshAnalytic
  have h1 := meshCompare_pos (ε := ε/4) (by positivity)
  have hμ := meshLossUnit_pos (ε := ε/4) (by positivity)
  have h2 := Cycle25.Energy.commonMesh_pos 2 28 1 (meshLossUnit (ε/4)/8) (by norm_num)
    (by norm_num) (by positivity)
  have h3 : 0 < min (meshLossUnit (ε/4)/8) (1*(902420521/120632400000:ℝ)/4) :=
    lt_min (by positivity) (by norm_num)
  have h4 := lt_min h2 h3
  have h5 := lt_min h1 h4
  positivity

theorem detectorMesh_pos {ε : ℝ} (hε : 0 < ε) : 0 < detectorMesh ε :=
  (OAI.SevenEighths.Cycle63MarkedPlain.marked_geometry_mesh_gates _
    (lt_min (meshAnalytic_pos hε) (meshCompare_pos (by positivity)))).1

end
end DetectorAffine
