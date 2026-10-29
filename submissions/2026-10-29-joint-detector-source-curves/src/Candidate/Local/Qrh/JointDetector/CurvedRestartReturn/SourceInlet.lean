/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.CurvedRestartReturn.Formulas
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.CurvedRestartReturn
open QRH.Record1252270103Return
noncomputable section

open QRH.Record12518109Source QRH.Record12518109Existence

def physicalGlobal : SourceFace := globalFace physicalB physicalLambda physicalCap

def countingSource (b : CountBranch) : SourceFace :=
 broadFace (branchB b) (branchL b) (branchCap b)

/-- The finite source bank is quantified before the ambient slot data. -/
def SourceBank : Prop := ∀ b : CountBranch, b ≠ .old →
 UniformUnitFaceSource (countingSource b)

theorem finite_sources_common_mesh (faces : List SourceFace)
 (hs : ∀ f ∈ faces, UniformUnitFaceSource f) {ε : ℝ} (hε : 0 < ε) :
 ∃ mesh : ℝ, 0 < mesh ∧ ∀ f ∈ faces, UnitFaceSource f mesh ε := by
 induction faces with
 | nil => exact ⟨1, by norm_num, by simp⟩
 | cons f fs ih =>
   obtain ⟨m, hm, hf⟩ := hs f (by simp) ε hε
   obtain ⟨n, hn, hfs⟩ := ih (fun g hg => hs g (by simp [hg]))
   refine ⟨min m n, lt_min hm hn, ?_⟩
   intro g hg
   rcases List.mem_cons.mp hg with rfl | hg
   · exact hf.mono_mesh (min_le_left _ _)
   · exact (hfs g hg).mono_mesh (min_le_right _ _)

end
end Qrh.JointDetector.CurvedRestartReturn
