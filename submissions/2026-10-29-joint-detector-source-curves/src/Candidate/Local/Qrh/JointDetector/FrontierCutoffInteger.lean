/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerState
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerBernstein
import Candidate.Local.Qrh.JointDetector.FrontierCertificateSemantic

namespace Qrh.JointDetector.FrontierCutoffInteger
open RepeatedMarks.SourceCurveInteger RepeatedMarks.SourceCurveCertificate
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

/-- The only changed integer gate for the smaller fixed selected gap. -/
def numerator (p : Params) : Fin 12 → ℤ :=
 ![1000000000*p.a0*(p.q0-p.eps)-500000001*p.q0*(p.den:ℤ),
   1000000000*(p.a0*(p.den:ℤ)+p.a1*(p.q0-p.eps))-500000001*(p.den:ℤ)^2,
   1000000000*(p.a1*(p.den:ℤ)+p.a2*(p.q0-p.eps)),
   1000000000*(p.a2*(p.den:ℤ)+p.a3*(p.q0-p.eps)),
   1000000000*p.a3*(p.den:ℤ),0,0,0,0,0,0,0]

theorem eval_numerator (p : Params) (u : ℝ) :
 eval (fun j => (numerator p j:ℝ)/(1000000000*(p.den:ℝ)^2)) u =
   (p.toReal.state u).a*(p.toReal.state u).n-
     (500000001/1000000000:ℝ)*(p.toReal.state u).q := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 norm_num [eval,Fin.sum_univ_succ,numerator,RealParams.state,Params.toReal,State.n]
 field_simp [hd]
 ring

theorem positive {p : Params} {lo hi : ℤ} (hw : lo<hi)
 (hn : ∀ i,0<bernsteinNumerator (numerator p) p.den lo hi i)
 {u : ℝ} (hu : u∈Set.Icc ((lo:ℝ)/(p.den:ℝ)) ((hi:ℝ)/(p.den:ℝ))) :
 0<FrontierSourceCurveCertificate.combined (p.toReal.state u) 3 := by
 have hd := p.den_pos
 have hp := positive_of_numerator p.den_pos
   (by positivity : 0<1000000000*p.den^2) hw hn hu
 simpa [eval_numerator,FrontierSourceCurveCertificate.combined] using hp

end
end Qrh.JointDetector.FrontierCutoffInteger
#print axioms Qrh.JointDetector.FrontierCutoffInteger.positive
