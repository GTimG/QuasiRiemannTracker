import Candidate.Local.Qrh.PositiveGap.Return.Constants
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PositiveGap.Return
open QRH.Record1252270103Return
noncomputable section
variable [TargetC]
open QRH.Record12518109Source QRH.Record12518109Existence
def countGlobal : SourceFace := globalFace countCB countCL countCap
def physicalGlobal : SourceFace := globalFace physicalB physicalLambda physicalCap
theorem selected_sources_common_mesh
    (hC : UniformUnitFaceSource countGlobal) (hP : UniformUnitFaceSource physicalGlobal)
    {ε : ℝ} (hε : 0<ε) :
    ∃mesh : ℝ,0<mesh ∧ UnitFaceSource countGlobal mesh ε ∧
      UnitFaceSource physicalGlobal mesh ε := by
  obtain ⟨c,hc,hcs⟩ := hC ε hε
  obtain ⟨p,hp,hps⟩ := hP ε hε
  exact ⟨min c p,lt_min hc hp,hcs.mono_mesh (min_le_left c p),hps.mono_mesh (min_le_right c p)⟩
end
end QRH.PositiveGap.Return
