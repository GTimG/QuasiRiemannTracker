import Candidate.Uneven.FineSchedule
import Candidate.Uneven.AuxiliaryCellGeometry
import Candidate.Cycle63.Physical.InitialMass.GeometryMeshChoice

/- Original module: Candidate.Uneven.AuxiliaryAssemblyMesh. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.AuxiliaryAssembly
open Cycle63InitialMass SaturatedPlain

def chosenMesh (ε : ℝ) : ℝ :=
  min (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
    (Cycle63FirstActual.comparisonMesh 1 1 (ε/2)))
    (min (Sil.Uneven.AuxiliarySource.amplifierMinimum/4) (fineRawMesh*fineRawCore/31))

theorem chosen_mesh_admission (ε : ℝ) (hε : 0<ε) :
    let μ:=geometryLossUnit 1 (ε/4)
    0<chosenMesh ε ∧
    chosenMesh ε≤Cycle63FirstActual.comparisonMesh 1 1 (ε/2) ∧
    chosenMesh ε≤Cycle25.Energy.commonMesh 2 28 1 (μ/8) ∧
    chosenMesh ε≤μ/8 ∧ chosenMesh ε<Sil.Uneven.AuxiliarySource.amplifierMinimum/2 ∧
    chosenMesh ε≤fineRawMesh*fineRawCore := by
  intro μ
  have ha:=geometry_analytic_mesh_admission 1 1 (ε/4) 2 28 1
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
  have hc:=Cycle63FirstActual.comparisonMesh_pos 1 1 (ε/2)
    (by norm_num) (by norm_num) (by positivity)
  have hf : 0<Sil.Uneven.AuxiliarySource.amplifierMinimum := by norm_num [Sil.Uneven.AuxiliarySource.amplifierMinimum]
  have hfm : 0 < fineRawMesh := fine_raw_mesh_gates.1
  have hfc : 0 < fineRawCore := by norm_num [fineRawCore]
  have hm : 0 < fineRawMesh*fineRawCore/31 := by positivity
  have hleft : chosenMesh ε ≤ min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
      (Cycle63FirstActual.comparisonMesh 1 1 (ε/2)) := min_le_left _ _
  have hright : chosenMesh ε ≤ min (Sil.Uneven.AuxiliarySource.amplifierMinimum/4)
      (fineRawMesh*fineRawCore/31) := min_le_right _ _
  have han:=hleft.trans (min_le_left _ _)
  have hamp:=hright.trans (min_le_left _ _)
  have hmark:=hright.trans (min_le_right _ _)
  have hpos : 0<chosenMesh ε := lt_min (lt_min ha.1 hc) (lt_min (by positivity) hm)
  refine ⟨hpos,hleft.trans (min_le_right _ _),han.trans ha.2.2.1,
    han.trans ha.2.2.2.1,by linarith only [hamp,hf],?_⟩
  exact hmark.trans (by nlinarith [mul_pos hfm hfc])

end OAI.SevenEighths.AuxiliaryAssembly
end

/- Original module: Candidate.Uneven.AuxiliaryAssemblySourceMesh. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
namespace OAI.SevenEighths.AuxiliaryAssembly
noncomputable section
/-- The fixed cap licenses the entire actual marked schedule. It is chosen
before the detector; final error monotonicity restores the requested error. -/
def cappedError (ε : ℝ) : ℝ := min ε (1/10000000000000000000000000000)
def sourceMesh (ε : ℝ) : ℝ := chosenMesh (cappedError ε)
theorem capped_error_bounds {ε : ℝ} (hε : 0<ε) :
    0<cappedError ε ∧ cappedError ε≤ε ∧
      cappedError ε≤1/10000000000000000000000000000 := by
  exact ⟨lt_min hε (by norm_num),min_le_left _ _,min_le_right _ _⟩
theorem source_mesh_pos {ε : ℝ} (hε : 0<ε) : 0<sourceMesh ε :=
  (chosen_mesh_admission (cappedError ε) (capped_error_bounds hε).1).1
end
end OAI.SevenEighths.AuxiliaryAssembly
end
