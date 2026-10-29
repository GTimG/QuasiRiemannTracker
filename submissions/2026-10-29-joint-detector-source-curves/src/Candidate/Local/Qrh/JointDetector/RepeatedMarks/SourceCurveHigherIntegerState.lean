/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerData
import Candidate.Local.Qrh.JointDetector.FrontierCertificateSemantic

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The literal scalar state represented by a degree-seven curve piece. -/
def RealParams.state (p : RealParams) (u : ℝ) : SourceCurveCertificate.State :=
 ⟨p.q0+u,p.y0+p.y1*u^1+p.y2*u^2+p.y3*u^3+p.y4*u^4+p.y5*u^5+p.y6*u^6+p.y7*u^7,
  -p.y1-2*p.y2*u^1-3*p.y3*u^2-4*p.y4*u^3-5*p.y5*u^4-6*p.y6*u^5-7*p.y7*u^6,
  p.a0+p.a1*u+p.a2*u^2+p.a3*u^3,p.eps,p.cap⟩

theorem commonGate_state (p : RealParams) (i : Fin 20) (u : ℝ) :
 commonGate p i u=(p.state u).common i := by
 fin_cases i <;>
  norm_num [commonGate,RealParams.state,SourceCurveCertificate.State.common,
   SourceCurveCertificate.State.n,SourceCurveCertificate.State.D,
   SourceCurveCertificate.State.S] <;> ring

theorem combinedGate_state (p : RealParams) (i : Fin 10) (u : ℝ) :
 combinedGate p i u=FrontierSourceCurveCertificate.combined (p.state u) i := by
 fin_cases i <;>
  norm_num [combinedGate,RealParams.state,FrontierSourceCurveCertificate.combined,SourceCurveCertificate.State.combined,
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
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
