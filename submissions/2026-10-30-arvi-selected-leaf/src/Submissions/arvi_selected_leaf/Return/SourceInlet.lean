/- Repeated marks: fork of Collet's final-stage module SourceInlet (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the two global faces are the count face C = (4967/5000, 49/20, 9999/100000)
and the physical face P = (9933999/10^7, 2451/1000, 31/500); the unused window faces
(`countWindow`, `physicalWindow`) and `source_on_root_interval` are removed. -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Submissions.arvi_selected_leaf.Return.Constants
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.ArviDensity.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

def countGlobal : SourceFace := globalFace countCB countCL countCap
def physicalGlobal : SourceFace := globalFace physicalB physicalLambda physicalCap

/-- One mesh, chosen before the ambient slot type and every live parameter,
works for both global sources. -/
theorem selected_sources_common_mesh
    (hC : UniformUnitFaceSource countGlobal) (hP : UniformUnitFaceSource physicalGlobal)
    {ε : ℝ} (hε : 0<ε) :
    ∃mesh : ℝ,0<mesh ∧ UnitFaceSource countGlobal mesh ε ∧
      UnitFaceSource physicalGlobal mesh ε := by
  obtain ⟨c,hc,hcs⟩ := hC ε hε
  obtain ⟨p,hp,hps⟩ := hP ε hε
  exact ⟨min c p,lt_min hc hp,hcs.mono_mesh (min_le_left c p),hps.mono_mesh (min_le_right c p)⟩
end
end QRH.ArviDensity.Return
