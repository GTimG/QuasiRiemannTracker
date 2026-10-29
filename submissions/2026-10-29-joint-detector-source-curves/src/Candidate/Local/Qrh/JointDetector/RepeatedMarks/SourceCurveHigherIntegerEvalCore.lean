/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerData
namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
open FractionArithmetic
def commonPower (p : Params) (i : Fin 20) (j : Fin 16) : Fraction :=
 ⟨commonNumerator p i j,denominator p,denominator_pos p⟩
def combinedPower (p : Params) (i : Fin 10) (j : Fin 16) : Fraction :=
 ⟨combinedNumerator p i j,denominator p,denominator_pos p⟩
def purePower (p : Params) (i : Fin 4) (j : Fin 16) : Fraction :=
 ⟨pureNumerator p i j,denominator p,denominator_pos p⟩
/-- Factor the shared positive denominator before expanding the polynomial. -/
theorem eval_mk (a : Fin 16→ℤ) (d : ℕ) (hd : 0<d) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(⟨a j,d,hd⟩:Fraction).evalR) u=
 SourceCurveHigherCertificate.eval (fun j=>(a j:ℝ)) u/(d:ℝ) := by
 change SourceCurveHigherCertificate.eval (fun j=>(a j:ℝ)/(d:ℝ)) u=_
 unfold SourceCurveHigherCertificate.eval
 simp_rw [div_mul_eq_mul_div]
 rw [Finset.sum_div]
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
