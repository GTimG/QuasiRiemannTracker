/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RestartReturn.FinalWindows
import Candidate.Local.Qrh.JointDetector.RestartReturn.WindowSources
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountScheme
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RestartReturn
open QRH.Record1252270103Return
noncomputable section

open QRH.Record12518109Source QRH.Record12518109Existence
noncomputable abbrev finalCountScheme : CountScheme where
 naturalκ := naturalK/6
 natural_lo := by norm_num [naturalK]
 natural_hi := by norm_num [naturalK]
 windows := finalAdmittedWindows

theorem ReturnCountWindow.toAdmitted_face (w : ReturnCountWindow) :
 w.toAdmitted.face = countingSource w.branch := rfl

theorem final_windows_common_mesh (hs : SourceBank)
 {ε : ℝ} (hε : 0 < ε) : ∃ mesh : ℝ, 0 < mesh ∧
 ∀ w ∈ finalCountScheme.windows, UnitFaceSource w.face mesh ε := by
 have hf : ∀ f ∈ returnWindows.map (fun w => countingSource w.branch),
     UniformUnitFaceSource f := by
   intro f hf
   obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hf
   exact hs w.branch w.nonold
 obtain ⟨mesh, hm, hmesh⟩ := finite_sources_common_mesh _ hf hε
 refine ⟨mesh, hm, ?_⟩
 intro w hw
 obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
 exact hmesh _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

end
end Qrh.JointDetector.RestartReturn
