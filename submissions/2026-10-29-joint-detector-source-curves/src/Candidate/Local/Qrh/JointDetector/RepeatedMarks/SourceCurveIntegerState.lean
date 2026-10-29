/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerData
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveCertificateSemantic

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The literal scalar state represented by a cubic curve piece. -/
def RealParams.state (p : RealParams) (u : ℝ) : SourceCurveCertificate.State :=
 ⟨p.q0+u,p.y0+p.y1*u+p.y2*u^2+p.y3*u^3,
  -p.y1-2*p.y2*u-3*p.y3*u^2,
  p.a0+p.a1*u+p.a2*u^2+p.a3*u^3,p.eps,p.cap⟩

theorem commonGate_state (p : RealParams) (i : Fin 20) (u : ℝ) :
 commonGate p i u=(p.state u).common i := by
 fin_cases i <;>
  norm_num [commonGate,RealParams.state,SourceCurveCertificate.State.common,
   SourceCurveCertificate.State.n,SourceCurveCertificate.State.D,
   SourceCurveCertificate.State.S] <;> ring

theorem combinedGate_state (p : RealParams) (i : Fin 10) (u : ℝ) :
 combinedGate p i u=(p.state u).combined i := by
 fin_cases i <;>
  norm_num [combinedGate,RealParams.state,SourceCurveCertificate.State.combined,
   SourceCurveCertificate.State.n,SourceCurveCertificate.State.D,
   SourceCurveCertificate.State.S,SourceCurveCertificate.State.derivative,
   SourceCurveCertificate.State.repeated,SourceCurveCertificate.State.selected] <;> ring

theorem pureGate_state (p : RealParams) (i : Fin 4) (u : ℝ) :
 pureGate p i u=(p.state u).pure i := by
 fin_cases i <;>
  norm_num [pureGate,RealParams.state,SourceCurveCertificate.State.pure,
   SourceCurveCertificate.State.n,SourceCurveCertificate.State.D,
   SourceCurveCertificate.State.S,SourceCurveCertificate.State.pureDerivative,
   SourceCurveCertificate.State.pureRepeated] <;> ring

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
