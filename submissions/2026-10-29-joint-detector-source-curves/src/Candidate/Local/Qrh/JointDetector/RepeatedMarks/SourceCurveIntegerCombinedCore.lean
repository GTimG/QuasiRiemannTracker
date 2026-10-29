/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerCasts
namespace Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
open FractionArithmetic
theorem eval_mk (a : Fin 12→ℤ) (d : ℕ) (hd : 0<d) (u : ℝ) :
 SourceCurveCertificate.eval (fun j=>(⟨a j,d,hd⟩:Fraction).evalR) u=
 SourceCurveCertificate.eval (fun j=>(a j:ℝ)) u/(d:ℝ) := by
 change SourceCurveCertificate.eval (fun j=>(a j:ℝ)/(d:ℝ)) u=_
 unfold SourceCurveCertificate.eval
 simp_rw [div_mul_eq_mul_div]
 rw [Finset.sum_div]

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
