/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/


/- Cheap gate identities grouped without changing their theorem bodies. -/

import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerEvalCore

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open FractionArithmetic

private theorem cast_combinedCoefficient0_0 (p : Params) : (combinedCoefficient0_0 p:ℝ)=((3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^5) + ((-1500030000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_combinedCoefficient0_1 (p : Params) : (combinedCoefficient0_1 p:ℝ)=((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

theorem eval_combinedPower0 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (0:Fin 10) j).evalR) u=combinedGate p.toReal (0:Fin 10) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (0:Fin 10) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(combinedNumerator p (0:Fin 10) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (combinedNumerator p (0:Fin 10)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((combinedCoefficient0_0 p:ℝ)*u^0+((combinedCoefficient0_1 p:ℝ)*u^1+(((0:ℤ):ℝ)*u^2+(((0:ℤ):ℝ)*u^3+(((0:ℤ):ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = combinedGate p.toReal (0:Fin 10) u*(denominator p:ℝ)
 rw [cast_combinedCoefficient0_0 p,cast_combinedCoefficient0_1 p]
 norm_num [denominator,scale,order,combinedGate,Params.toReal]
 field_simp [hd]
 ring
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger


namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open FractionArithmetic

private theorem cast_combinedCoefficient1_0 (p : Params) : (combinedCoefficient1_0 p:ℝ)=((3000000000:ℝ)*(p.a0:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_combinedCoefficient1_1 (p : Params) : (combinedCoefficient1_1 p:ℝ)=((3000000000:ℝ)*(p.a1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_combinedCoefficient1_2 (p : Params) : (combinedCoefficient1_2 p:ℝ)=((3000000000:ℝ)*(p.a2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_combinedCoefficient1_3 (p : Params) : (combinedCoefficient1_3 p:ℝ)=((3000000000:ℝ)*(p.a3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_combinedPower1 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (1:Fin 10) j).evalR) u=combinedGate p.toReal (1:Fin 10) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (1:Fin 10) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(combinedNumerator p (1:Fin 10) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (combinedNumerator p (1:Fin 10)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((combinedCoefficient1_0 p:ℝ)*u^0+((combinedCoefficient1_1 p:ℝ)*u^1+((combinedCoefficient1_2 p:ℝ)*u^2+((combinedCoefficient1_3 p:ℝ)*u^3+(((0:ℤ):ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = combinedGate p.toReal (1:Fin 10) u*(denominator p:ℝ)
 rw [cast_combinedCoefficient1_0 p,cast_combinedCoefficient1_1 p,cast_combinedCoefficient1_2 p,cast_combinedCoefficient1_3 p]
 norm_num [denominator,scale,order,combinedGate,Params.toReal]
 field_simp [hd]
 ring
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger


namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open FractionArithmetic

private theorem cast_combinedCoefficient2_0 (p : Params) : (combinedCoefficient2_0 p:ℝ)=((3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.a0:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_combinedCoefficient2_1 (p : Params) : (combinedCoefficient2_1 p:ℝ)=((-3000000000:ℝ)*(p.a1:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_combinedCoefficient2_2 (p : Params) : (combinedCoefficient2_2 p:ℝ)=((-3000000000:ℝ)*(p.a2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_combinedCoefficient2_3 (p : Params) : (combinedCoefficient2_3 p:ℝ)=((-3000000000:ℝ)*(p.a3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_combinedPower2 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (2:Fin 10) j).evalR) u=combinedGate p.toReal (2:Fin 10) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (2:Fin 10) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(combinedNumerator p (2:Fin 10) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (combinedNumerator p (2:Fin 10)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((combinedCoefficient2_0 p:ℝ)*u^0+((combinedCoefficient2_1 p:ℝ)*u^1+((combinedCoefficient2_2 p:ℝ)*u^2+((combinedCoefficient2_3 p:ℝ)*u^3+(((0:ℤ):ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = combinedGate p.toReal (2:Fin 10) u*(denominator p:ℝ)
 rw [cast_combinedCoefficient2_0 p,cast_combinedCoefficient2_1 p,cast_combinedCoefficient2_2 p,cast_combinedCoefficient2_3 p]
 norm_num [denominator,scale,order,combinedGate,Params.toReal]
 field_simp [hd]
 ring
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger


namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open FractionArithmetic

private theorem cast_combinedCoefficient3_0 (p : Params) : (combinedCoefficient3_0 p:ℝ)=((3000000000:ℝ)*(p.q0:ℝ)*(p.a0:ℝ)*(p.den:ℝ)^4) + ((-1500000003:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.a0:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) := by
 norm_cast

private theorem cast_combinedCoefficient3_1 (p : Params) : (combinedCoefficient3_1 p:ℝ)=((3000000000:ℝ)*(p.q0:ℝ)*(p.a1:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.a0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.a1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-1500000003:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_combinedCoefficient3_2 (p : Params) : (combinedCoefficient3_2 p:ℝ)=((3000000000:ℝ)*(p.q0:ℝ)*(p.a2:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.a1:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.a2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) := by
 norm_cast

private theorem cast_combinedCoefficient3_3 (p : Params) : (combinedCoefficient3_3 p:ℝ)=((3000000000:ℝ)*(p.q0:ℝ)*(p.a3:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.a2:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.a3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) := by
 norm_cast

private theorem cast_combinedCoefficient3_4 (p : Params) : (combinedCoefficient3_4 p:ℝ)=((3000000000:ℝ)*(p.a3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_combinedPower3 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (3:Fin 10) j).evalR) u=combinedGate p.toReal (3:Fin 10) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(combinedPower p (3:Fin 10) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(combinedNumerator p (3:Fin 10) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (combinedNumerator p (3:Fin 10)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((combinedCoefficient3_0 p:ℝ)*u^0+((combinedCoefficient3_1 p:ℝ)*u^1+((combinedCoefficient3_2 p:ℝ)*u^2+((combinedCoefficient3_3 p:ℝ)*u^3+((combinedCoefficient3_4 p:ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = combinedGate p.toReal (3:Fin 10) u*(denominator p:ℝ)
 rw [cast_combinedCoefficient3_0 p,cast_combinedCoefficient3_1 p,cast_combinedCoefficient3_2 p,cast_combinedCoefficient3_3 p,cast_combinedCoefficient3_4 p]
 norm_num [denominator,scale,order,combinedGate,Params.toReal]
 field_simp [hd]
 ring
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
