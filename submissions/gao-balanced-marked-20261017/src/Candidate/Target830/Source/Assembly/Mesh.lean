import Candidate.Target830.Marked.Schedule
import Candidate.Target830.Source.Schedule
import Candidate.Cycle63.Physical.InitialMass.GeometryMeshChoice

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open Cycle63InitialMass Marked830Plain

/-- The same strictly positive source mesh serves both finite source planes,
before the detector dictionary and its cardinality are chosen. -/
def chosenMesh (ε : ℝ) : ℝ :=
  min (geometryMesh830 (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
    (Cycle63FirstActual.comparisonMesh 1 1 (ε/2)))) (amplifierMinimum/4)

theorem chosen_mesh_admission (ε : ℝ) (hε : 0<ε) :
    let μ:=geometryLossUnit 1 (ε/4)
    0<chosenMesh ε ∧
    chosenMesh ε≤Cycle63FirstActual.comparisonMesh 1 1 (ε/2) ∧
    chosenMesh ε≤Cycle25.Energy.commonMesh 2 28 1 (μ/8) ∧
    chosenMesh ε≤μ/8 ∧ chosenMesh ε<amplifierMinimum/2 ∧
    chosenMesh ε≤rawMesh830*rawCore830 := by
  intro μ
  have ha:=geometry_analytic_mesh_admission 1 1 (ε/4) 2 28 1
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
  have hc:=Cycle63FirstActual.comparisonMesh_pos 1 1 (ε/2)
    (by norm_num) (by norm_num) (by positivity)
  have hg:=geometry_mesh830_gates
    (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
      (Cycle63FirstActual.comparisonMesh 1 1 (ε/2))) (lt_min ha.1 hc)
  have hf : 0<amplifierMinimum := by norm_num [amplifierMinimum]
  have hleft : chosenMesh ε≤geometryMesh830
      (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
        (Cycle63FirstActual.comparisonMesh 1 1 (ε/2))) := min_le_left _ _
  have hcap : chosenMesh ε≤amplifierMinimum/4 := min_le_right _ _
  have hbase:=hleft.trans hg.2.1
  have han:=hbase.trans (min_le_left _ _)
  have hpos : 0<chosenMesh ε:=lt_min hg.1 (by positivity)
  refine ⟨hpos,hbase.trans (min_le_right _ _),han.trans ha.2.2.1,
    han.trans ha.2.2.2.1,by linarith,?_⟩
  have h31:=hg.2.2
  have h1 : chosenMesh ε≤31*geometryMesh830
      (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
        (Cycle63FirstActual.comparisonMesh 1 1 (ε/2))) := by linarith [hg.1]
  exact h1.trans h31

end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.chosen_mesh_admission
