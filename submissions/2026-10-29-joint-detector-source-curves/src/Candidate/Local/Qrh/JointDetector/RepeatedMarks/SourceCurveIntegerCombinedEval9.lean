/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerCombinedCore
namespace Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
noncomputable section
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
open FractionArithmetic
theorem eval_combinedPower9 (p : Params) (u : ℝ) :
 SourceCurveCertificate.eval (fun j=>(combinedPower p (9:Fin 10) j).evalR) u=combinedGate p.toReal (9:Fin 10) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveCertificate.eval (fun j=>(combinedPower p (9:Fin 10) j).evalR) u=
   SourceCurveCertificate.eval (fun j=>(combinedNumerator p (9:Fin 10) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (combinedNumerator p (9:Fin 10)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((combinedCoefficient9_0 p:ℝ)*u^0+((combinedCoefficient9_1 p:ℝ)*u^1+((combinedCoefficient9_2 p:ℝ)*u^2+((combinedCoefficient9_3 p:ℝ)*u^3+((combinedCoefficient9_4 p:ℝ)*u^4+((combinedCoefficient9_5 p:ℝ)*u^5+((combinedCoefficient9_6 p:ℝ)*u^6+((combinedCoefficient9_7 p:ℝ)*u^7+((combinedCoefficient9_8 p:ℝ)*u^8+((combinedCoefficient9_9 p:ℝ)*u^9+((combinedCoefficient9_10 p:ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(0:ℝ))))))))))))) = combinedGate p.toReal (9:Fin 10) u*(denominator p:ℝ)
 rw [cast_combinedCoefficient9_0 p,cast_combinedCoefficient9_1 p,cast_combinedCoefficient9_2 p,cast_combinedCoefficient9_3 p,cast_combinedCoefficient9_4 p,cast_combinedCoefficient9_5 p,cast_combinedCoefficient9_6 p,cast_combinedCoefficient9_7 p,cast_combinedCoefficient9_8 p,cast_combinedCoefficient9_9 p,cast_combinedCoefficient9_10 p]
 norm_num [-cast_combinedCoefficient0_0,-cast_combinedCoefficient0_1,-cast_combinedCoefficient1_0,-cast_combinedCoefficient1_1,-cast_combinedCoefficient1_2,-cast_combinedCoefficient1_3,-cast_combinedCoefficient2_0,-cast_combinedCoefficient2_1,-cast_combinedCoefficient2_2,-cast_combinedCoefficient2_3,-cast_combinedCoefficient3_0,-cast_combinedCoefficient3_1,-cast_combinedCoefficient3_2,-cast_combinedCoefficient3_3,-cast_combinedCoefficient3_4,-cast_combinedCoefficient4_0,-cast_combinedCoefficient4_1,-cast_combinedCoefficient4_2,-cast_combinedCoefficient4_3,-cast_combinedCoefficient4_4,-cast_combinedCoefficient4_5,-cast_combinedCoefficient4_6,-cast_combinedCoefficient4_7,-cast_combinedCoefficient4_8,-cast_combinedCoefficient5_0,-cast_combinedCoefficient5_1,-cast_combinedCoefficient5_2,-cast_combinedCoefficient5_3,-cast_combinedCoefficient5_4,-cast_combinedCoefficient5_5,-cast_combinedCoefficient5_6,-cast_combinedCoefficient5_7,-cast_combinedCoefficient5_8,-cast_combinedCoefficient5_9,-cast_combinedCoefficient5_10,-cast_combinedCoefficient5_11,-cast_combinedCoefficient6_0,-cast_combinedCoefficient6_1,-cast_combinedCoefficient6_2,-cast_combinedCoefficient6_3,-cast_combinedCoefficient6_4,-cast_combinedCoefficient6_5,-cast_combinedCoefficient6_6,-cast_combinedCoefficient6_7,-cast_combinedCoefficient6_8,-cast_combinedCoefficient6_9,-cast_combinedCoefficient6_10,-cast_combinedCoefficient6_11,-cast_combinedCoefficient7_0,-cast_combinedCoefficient7_1,-cast_combinedCoefficient7_2,-cast_combinedCoefficient7_3,-cast_combinedCoefficient7_4,-cast_combinedCoefficient7_5,-cast_combinedCoefficient7_6,-cast_combinedCoefficient7_7,-cast_combinedCoefficient8_0,-cast_combinedCoefficient8_1,-cast_combinedCoefficient8_2,-cast_combinedCoefficient8_3,-cast_combinedCoefficient8_4,-cast_combinedCoefficient8_5,-cast_combinedCoefficient8_6,-cast_combinedCoefficient8_7,-cast_combinedCoefficient8_8,-cast_combinedCoefficient8_9,-cast_combinedCoefficient8_10,-cast_combinedCoefficient9_0,-cast_combinedCoefficient9_1,-cast_combinedCoefficient9_2,-cast_combinedCoefficient9_3,-cast_combinedCoefficient9_4,-cast_combinedCoefficient9_5,-cast_combinedCoefficient9_6,-cast_combinedCoefficient9_7,-cast_combinedCoefficient9_8,-cast_combinedCoefficient9_9,-cast_combinedCoefficient9_10,denominator,scale,order,combinedGate,Params.toReal]
 field_simp [hd]
 ring
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
