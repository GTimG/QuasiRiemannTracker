/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
/- Repeated marks: fork of Collet's final-stage module SourceInlet (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the two global faces are the count face C = (4967/5000, 49/20, 9999/100000)
and the physical face P = (9933999/10^7, 2451/1000, 31/500); the unused window faces
(`countWindow`, `physicalWindow`) and `source_on_root_interval` are removed. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Constants
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Qrh.JointDetector.PointwiseReturn
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

def countGlobal : SourceFace := globalFace countCB countCL countCap
def physicalGlobal : SourceFace := globalFace physicalB physicalLambda countCap

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
end Qrh.JointDetector.PointwiseReturn
