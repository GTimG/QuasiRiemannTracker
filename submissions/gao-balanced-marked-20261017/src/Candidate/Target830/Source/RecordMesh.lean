import Candidate.Target830.Source.Assembly.SourceMesh
import Candidate.Target830.Physical.Chosen

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.RecordEndpoint
noncomputable section
/-- This single positive mesh is fixed before choosing the detector, slots,
profiles or finite dictionary. It serves both source uses of the same data. -/
def commonSourceMesh (ε t : ℝ) : ℝ :=
  min (Assembly.sourceMesh t) (Assembly.sourceMesh ε)

theorem common_source_mesh_pos {ε t : ℝ} (hε : 0<ε) (ht : 0<t) :
    0<commonSourceMesh ε t :=
  lt_min (Assembly.source_mesh_pos ht) (Assembly.source_mesh_pos hε)

end
end OAI.SevenEighths.Target830.Source.RecordEndpoint
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.common_source_mesh_pos
