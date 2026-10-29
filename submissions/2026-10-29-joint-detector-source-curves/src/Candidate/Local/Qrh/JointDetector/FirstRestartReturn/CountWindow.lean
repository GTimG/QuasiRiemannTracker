/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
/- Repeated marks: fork of Collet's final-stage module CountWindows (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): only the window structure is kept here; the generated windows and
their admission certificates are in `Windows.lean` and `Rows/AdmissionNN.lean`. -/
import Candidate.Local.Qrh.JointDetector.FirstRestartReturn.CountMonotonicity
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountingBridge
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Qrh.JointDetector.FirstRestartReturn
open QRH.Record1252270103Return
noncomputable section

structure ReturnCountWindow where
 branch : CountBranch
 nonold : branch≠.old
 deltaLo : ℝ
 deltaHi : ℝ
 pLo : ℝ
 deltaBounds : 0≤deltaLo ∧ deltaHi≤3/4
 pBounds : 0≤pLo ∧ pLo≤1/2
 certificate : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  ∀j:Fin 15,0<admissionGuard branch δ p j

def ReturnCountWindow.Available (w : ReturnCountWindow) (δ p : ℝ) : Prop :=
 δ∈Set.Icc w.deltaLo w.deltaHi ∧ p∈Set.Icc w.pLo (1/2)
theorem ReturnCountWindow.upward (w : ReturnCountWindow) {δ p q:ℝ}
 (hp:w.Available δ p) (hpq:p≤q) (hq:q≤1/2) : w.Available δ q :=
 ⟨hp.1,⟨hp.2.1.trans hpq,hq⟩⟩
theorem ReturnCountWindow.antitone (w : ReturnCountWindow) {δ:ℝ}
 (hδ:δ∈Set.Icc w.deltaLo w.deltaHi) :
 AntitoneOn (branchCount w.branch δ) (Set.Icc w.pLo (1/2)) :=
 branchCount_antitoneOn w.branch w.nonold (w.deltaBounds.1.trans hδ.1)
  (by linarith [hδ.2,w.deltaBounds.2]) (fun _ hp=>w.certificate hδ hp)
def ReturnCountWindow.toBranch (w : ReturnCountWindow) : Branch where
 available := w.Available
 value := branchCount w.branch
 upward := w.upward
 antitone := by
  intro δ p q hp hq hpq
  exact w.antitone hp.1 hp.2 hq.2 hpq
end
end Qrh.JointDetector.FirstRestartReturn
