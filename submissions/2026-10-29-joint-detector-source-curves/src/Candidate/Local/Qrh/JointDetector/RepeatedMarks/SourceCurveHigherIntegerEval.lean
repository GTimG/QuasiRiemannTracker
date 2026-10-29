/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCommonEvalCompact
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerPureEvalCompact
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCombinedEvalCompact
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCombinedEval4
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCombinedEval5
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCombinedEval6
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCombinedEval7
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCombinedEval8
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerCombinedEval9
namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
theorem eval_commonPower (p : Params) (i : Fin 20) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p i j).evalR) u=commonGate p.toReal i u := by
 fin_cases i
 · exact eval_commonPower0 p u
 · exact eval_commonPower1 p u
 · exact eval_commonPower2 p u
 · exact eval_commonPower3 p u
 · exact eval_commonPower4 p u
 · exact eval_commonPower5 p u
 · exact eval_commonPower6 p u
 · exact eval_commonPower7 p u
 · exact eval_commonPower8 p u
 · exact eval_commonPower9 p u
 · exact eval_commonPower10 p u
 · exact eval_commonPower11 p u
 · exact eval_commonPower12 p u
 · exact eval_commonPower13 p u
 · exact eval_commonPower14 p u
 · exact eval_commonPower15 p u
 · exact eval_commonPower16 p u
 · exact eval_commonPower17 p u
 · exact eval_commonPower18 p u
 · exact eval_commonPower19 p u

theorem eval_combinedPower (p : Params) (i : Fin 10) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(combinedPower p i j).evalR) u=combinedGate p.toReal i u := by
 fin_cases i
 · exact eval_combinedPower0 p u
 · exact eval_combinedPower1 p u
 · exact eval_combinedPower2 p u
 · exact eval_combinedPower3 p u
 · exact eval_combinedPower4 p u
 · exact eval_combinedPower5 p u
 · exact eval_combinedPower6 p u
 · exact eval_combinedPower7 p u
 · exact eval_combinedPower8 p u
 · exact eval_combinedPower9 p u

theorem eval_purePower (p : Params) (i : Fin 4) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(purePower p i j).evalR) u=pureGate p.toReal i u := by
 fin_cases i
 · exact eval_purePower0 p u
 · exact eval_purePower1 p u
 · exact eval_purePower2 p u
 · exact eval_purePower3 p u

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger.eval_combinedPower
