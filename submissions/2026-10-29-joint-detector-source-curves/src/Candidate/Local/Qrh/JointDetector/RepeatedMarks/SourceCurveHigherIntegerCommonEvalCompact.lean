/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/


/- Cheap gate identities grouped without changing their theorem bodies. -/

import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerEvalCore

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open FractionArithmetic

private theorem cast_commonCoefficient0_0 (p : Params) : (commonCoefficient0_0 p:ℝ)=((3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^5) + ((-1200000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient0_1 (p : Params) : (commonCoefficient0_1 p:ℝ)=((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

theorem eval_commonPower0 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (0:Fin 20) j).evalR) u=commonGate p.toReal (0:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (0:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (0:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (0:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient0_0 p:ℝ)*u^0+((commonCoefficient0_1 p:ℝ)*u^1+(((0:ℤ):ℝ)*u^2+(((0:ℤ):ℝ)*u^3+(((0:ℤ):ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (0:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient0_0 p,cast_commonCoefficient0_1 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient1_0 (p : Params) : (commonCoefficient1_0 p:ℝ)=((-3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((2250000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient1_1 (p : Params) : (commonCoefficient1_1 p:ℝ)=((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

theorem eval_commonPower1 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (1:Fin 20) j).evalR) u=commonGate p.toReal (1:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (1:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (1:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (1:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient1_0 p:ℝ)*u^0+((commonCoefficient1_1 p:ℝ)*u^1+(((0:ℤ):ℝ)*u^2+(((0:ℤ):ℝ)*u^3+(((0:ℤ):ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (1:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient1_0 p,cast_commonCoefficient1_1 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient2_0 (p : Params) : (commonCoefficient2_0 p:ℝ)=((3000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient2_1 (p : Params) : (commonCoefficient2_1 p:ℝ)=((3000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient2_2 (p : Params) : (commonCoefficient2_2 p:ℝ)=((3000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient2_3 (p : Params) : (commonCoefficient2_3 p:ℝ)=((3000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient2_4 (p : Params) : (commonCoefficient2_4 p:ℝ)=((3000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient2_5 (p : Params) : (commonCoefficient2_5 p:ℝ)=((3000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient2_6 (p : Params) : (commonCoefficient2_6 p:ℝ)=((3000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient2_7 (p : Params) : (commonCoefficient2_7 p:ℝ)=((3000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower2 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (2:Fin 20) j).evalR) u=commonGate p.toReal (2:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (2:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (2:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (2:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient2_0 p:ℝ)*u^0+((commonCoefficient2_1 p:ℝ)*u^1+((commonCoefficient2_2 p:ℝ)*u^2+((commonCoefficient2_3 p:ℝ)*u^3+((commonCoefficient2_4 p:ℝ)*u^4+((commonCoefficient2_5 p:ℝ)*u^5+((commonCoefficient2_6 p:ℝ)*u^6+((commonCoefficient2_7 p:ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (2:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient2_0 p,cast_commonCoefficient2_1 p,cast_commonCoefficient2_2 p,cast_commonCoefficient2_3 p,cast_commonCoefficient2_4 p,cast_commonCoefficient2_5 p,cast_commonCoefficient2_6 p,cast_commonCoefficient2_7 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient3_0 (p : Params) : (commonCoefficient3_0 p:ℝ)=((-3000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient3_1 (p : Params) : (commonCoefficient3_1 p:ℝ)=((-3000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient3_2 (p : Params) : (commonCoefficient3_2 p:ℝ)=((-3000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient3_3 (p : Params) : (commonCoefficient3_3 p:ℝ)=((-3000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient3_4 (p : Params) : (commonCoefficient3_4 p:ℝ)=((-3000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient3_5 (p : Params) : (commonCoefficient3_5 p:ℝ)=((-3000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient3_6 (p : Params) : (commonCoefficient3_6 p:ℝ)=((-3000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient3_7 (p : Params) : (commonCoefficient3_7 p:ℝ)=((-3000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower3 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (3:Fin 20) j).evalR) u=commonGate p.toReal (3:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (3:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (3:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (3:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient3_0 p:ℝ)*u^0+((commonCoefficient3_1 p:ℝ)*u^1+((commonCoefficient3_2 p:ℝ)*u^2+((commonCoefficient3_3 p:ℝ)*u^3+((commonCoefficient3_4 p:ℝ)*u^4+((commonCoefficient3_5 p:ℝ)*u^5+((commonCoefficient3_6 p:ℝ)*u^6+((commonCoefficient3_7 p:ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (3:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient3_0 p,cast_commonCoefficient3_1 p,cast_commonCoefficient3_2 p,cast_commonCoefficient3_3 p,cast_commonCoefficient3_4 p,cast_commonCoefficient3_5 p,cast_commonCoefficient3_6 p,cast_commonCoefficient3_7 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient4_0 (p : Params) : (commonCoefficient4_0 p:ℝ)=((-3000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient4_1 (p : Params) : (commonCoefficient4_1 p:ℝ)=((-6000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient4_2 (p : Params) : (commonCoefficient4_2 p:ℝ)=((-9000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient4_3 (p : Params) : (commonCoefficient4_3 p:ℝ)=((-12000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient4_4 (p : Params) : (commonCoefficient4_4 p:ℝ)=((-15000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient4_5 (p : Params) : (commonCoefficient4_5 p:ℝ)=((-18000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient4_6 (p : Params) : (commonCoefficient4_6 p:ℝ)=((-21000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower4 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (4:Fin 20) j).evalR) u=commonGate p.toReal (4:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (4:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (4:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (4:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient4_0 p:ℝ)*u^0+((commonCoefficient4_1 p:ℝ)*u^1+((commonCoefficient4_2 p:ℝ)*u^2+((commonCoefficient4_3 p:ℝ)*u^3+((commonCoefficient4_4 p:ℝ)*u^4+((commonCoefficient4_5 p:ℝ)*u^5+((commonCoefficient4_6 p:ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (4:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient4_0 p,cast_commonCoefficient4_1 p,cast_commonCoefficient4_2 p,cast_commonCoefficient4_3 p,cast_commonCoefficient4_4 p,cast_commonCoefficient4_5 p,cast_commonCoefficient4_6 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient5_0 (p : Params) : (commonCoefficient5_0 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) := by
 norm_cast

private theorem cast_commonCoefficient5_1 (p : Params) : (commonCoefficient5_1 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-36000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) := by
 norm_cast

private theorem cast_commonCoefficient5_2 (p : Params) : (commonCoefficient5_2 p:ℝ)=((-54000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-72000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient5_3 (p : Params) : (commonCoefficient5_3 p:ℝ)=((-72000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-108000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient5_4 (p : Params) : (commonCoefficient5_4 p:ℝ)=((-90000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-144000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-54000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient5_5 (p : Params) : (commonCoefficient5_5 p:ℝ)=((-108000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-180000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-72000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient5_6 (p : Params) : (commonCoefficient5_6 p:ℝ)=((-126000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-216000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-90000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient5_7 (p : Params) : (commonCoefficient5_7 p:ℝ)=((-252000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-108000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient5_8 (p : Params) : (commonCoefficient5_8 p:ℝ)=((-126000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower5 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (5:Fin 20) j).evalR) u=commonGate p.toReal (5:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (5:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (5:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (5:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient5_0 p:ℝ)*u^0+((commonCoefficient5_1 p:ℝ)*u^1+((commonCoefficient5_2 p:ℝ)*u^2+((commonCoefficient5_3 p:ℝ)*u^3+((commonCoefficient5_4 p:ℝ)*u^4+((commonCoefficient5_5 p:ℝ)*u^5+((commonCoefficient5_6 p:ℝ)*u^6+((commonCoefficient5_7 p:ℝ)*u^7+((commonCoefficient5_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (5:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient5_0 p,cast_commonCoefficient5_1 p,cast_commonCoefficient5_2 p,cast_commonCoefficient5_3 p,cast_commonCoefficient5_4 p,cast_commonCoefficient5_5 p,cast_commonCoefficient5_6 p,cast_commonCoefficient5_7 p,cast_commonCoefficient5_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient6_0 (p : Params) : (commonCoefficient6_0 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^4) + ((-3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient6_1 (p : Params) : (commonCoefficient6_1 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient6_2 (p : Params) : (commonCoefficient6_2 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient6_3 (p : Params) : (commonCoefficient6_3 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient6_4 (p : Params) : (commonCoefficient6_4 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient6_5 (p : Params) : (commonCoefficient6_5 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient6_6 (p : Params) : (commonCoefficient6_6 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient6_7 (p : Params) : (commonCoefficient6_7 p:ℝ)=((18000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient6_8 (p : Params) : (commonCoefficient6_8 p:ℝ)=((18000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower6 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (6:Fin 20) j).evalR) u=commonGate p.toReal (6:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (6:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (6:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (6:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient6_0 p:ℝ)*u^0+((commonCoefficient6_1 p:ℝ)*u^1+((commonCoefficient6_2 p:ℝ)*u^2+((commonCoefficient6_3 p:ℝ)*u^3+((commonCoefficient6_4 p:ℝ)*u^4+((commonCoefficient6_5 p:ℝ)*u^5+((commonCoefficient6_6 p:ℝ)*u^6+((commonCoefficient6_7 p:ℝ)*u^7+((commonCoefficient6_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (6:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient6_0 p,cast_commonCoefficient6_1 p,cast_commonCoefficient6_2 p,cast_commonCoefficient6_3 p,cast_commonCoefficient6_4 p,cast_commonCoefficient6_5 p,cast_commonCoefficient6_6 p,cast_commonCoefficient6_7 p,cast_commonCoefficient6_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient7_0 (p : Params) : (commonCoefficient7_0 p:ℝ)=((-3000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((-3000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-3000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_1 (p : Params) : (commonCoefficient7_1 p:ℝ)=((-6000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-6000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-6000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-6000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_2 (p : Params) : (commonCoefficient7_2 p:ℝ)=((-9000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-12000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-9000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-3000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((-9000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_3 (p : Params) : (commonCoefficient7_3 p:ℝ)=((-12000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-12000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-6000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((-12000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_4 (p : Params) : (commonCoefficient7_4 p:ℝ)=((-15000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-24000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-15000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-9000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((-15000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_5 (p : Params) : (commonCoefficient7_5 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-30000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-12000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((-18000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_6 (p : Params) : (commonCoefficient7_6 p:ℝ)=((-21000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-36000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-21000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-15000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((-21000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_7 (p : Params) : (commonCoefficient7_7 p:ℝ)=((-42000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((-24000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient7_8 (p : Params) : (commonCoefficient7_8 p:ℝ)=((-21000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower7 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (7:Fin 20) j).evalR) u=commonGate p.toReal (7:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (7:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (7:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (7:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient7_0 p:ℝ)*u^0+((commonCoefficient7_1 p:ℝ)*u^1+((commonCoefficient7_2 p:ℝ)*u^2+((commonCoefficient7_3 p:ℝ)*u^3+((commonCoefficient7_4 p:ℝ)*u^4+((commonCoefficient7_5 p:ℝ)*u^5+((commonCoefficient7_6 p:ℝ)*u^6+((commonCoefficient7_7 p:ℝ)*u^7+((commonCoefficient7_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (7:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient7_0 p,cast_commonCoefficient7_1 p,cast_commonCoefficient7_2 p,cast_commonCoefficient7_3 p,cast_commonCoefficient7_4 p,cast_commonCoefficient7_5 p,cast_commonCoefficient7_6 p,cast_commonCoefficient7_7 p,cast_commonCoefficient7_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient8_0 (p : Params) : (commonCoefficient8_0 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^2) + ((3000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((3000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_1 (p : Params) : (commonCoefficient8_1 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^2) + ((6000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-36000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((6000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_2 (p : Params) : (commonCoefficient8_2 p:ℝ)=((-54000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^2) + ((9000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-72000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((12000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((9000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((9000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_3 (p : Params) : (commonCoefficient8_3 p:ℝ)=((-72000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^2) + ((12000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-108000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((12000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_4 (p : Params) : (commonCoefficient8_4 p:ℝ)=((-90000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^2) + ((15000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-144000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((24000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-54000000000:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((9000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((15000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_5 (p : Params) : (commonCoefficient8_5 p:ℝ)=((-108000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^2) + ((18000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-180000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((30000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-72000000000:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((18000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_6 (p : Params) : (commonCoefficient8_6 p:ℝ)=((-126000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^2) + ((21000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-216000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((36000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((21000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-90000000000:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((21000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_7 (p : Params) : (commonCoefficient8_7 p:ℝ)=((-252000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((42000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-108000000000:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((24000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient8_8 (p : Params) : (commonCoefficient8_8 p:ℝ)=((-126000000000:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((21000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower8 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (8:Fin 20) j).evalR) u=commonGate p.toReal (8:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (8:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (8:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (8:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient8_0 p:ℝ)*u^0+((commonCoefficient8_1 p:ℝ)*u^1+((commonCoefficient8_2 p:ℝ)*u^2+((commonCoefficient8_3 p:ℝ)*u^3+((commonCoefficient8_4 p:ℝ)*u^4+((commonCoefficient8_5 p:ℝ)*u^5+((commonCoefficient8_6 p:ℝ)*u^6+((commonCoefficient8_7 p:ℝ)*u^7+((commonCoefficient8_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (8:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient8_0 p,cast_commonCoefficient8_1 p,cast_commonCoefficient8_2 p,cast_commonCoefficient8_3 p,cast_commonCoefficient8_4 p,cast_commonCoefficient8_5 p,cast_commonCoefficient8_6 p,cast_commonCoefficient8_7 p,cast_commonCoefficient8_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient9_0 (p : Params) : (commonCoefficient9_0 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient9_1 (p : Params) : (commonCoefficient9_1 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-36000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) := by
 norm_cast

private theorem cast_commonCoefficient9_2 (p : Params) : (commonCoefficient9_2 p:ℝ)=((-54000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-72000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient9_3 (p : Params) : (commonCoefficient9_3 p:ℝ)=((-72000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-108000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient9_4 (p : Params) : (commonCoefficient9_4 p:ℝ)=((-90000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-144000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-54000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient9_5 (p : Params) : (commonCoefficient9_5 p:ℝ)=((-108000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-180000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-72000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient9_6 (p : Params) : (commonCoefficient9_6 p:ℝ)=((-126000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-216000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-90000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient9_7 (p : Params) : (commonCoefficient9_7 p:ℝ)=((-252000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-108000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient9_8 (p : Params) : (commonCoefficient9_8 p:ℝ)=((-126000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower9 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (9:Fin 20) j).evalR) u=commonGate p.toReal (9:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (9:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (9:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (9:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient9_0 p:ℝ)*u^0+((commonCoefficient9_1 p:ℝ)*u^1+((commonCoefficient9_2 p:ℝ)*u^2+((commonCoefficient9_3 p:ℝ)*u^3+((commonCoefficient9_4 p:ℝ)*u^4+((commonCoefficient9_5 p:ℝ)*u^5+((commonCoefficient9_6 p:ℝ)*u^6+((commonCoefficient9_7 p:ℝ)*u^7+((commonCoefficient9_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (9:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient9_0 p,cast_commonCoefficient9_1 p,cast_commonCoefficient9_2 p,cast_commonCoefficient9_3 p,cast_commonCoefficient9_4 p,cast_commonCoefficient9_5 p,cast_commonCoefficient9_6 p,cast_commonCoefficient9_7 p,cast_commonCoefficient9_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient10_0 (p : Params) : (commonCoefficient10_0 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient10_1 (p : Params) : (commonCoefficient10_1 p:ℝ)=((-18000000000:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

theorem eval_commonPower10 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (10:Fin 20) j).evalR) u=commonGate p.toReal (10:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (10:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (10:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (10:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient10_0 p:ℝ)*u^0+((commonCoefficient10_1 p:ℝ)*u^1+(((0:ℤ):ℝ)*u^2+(((0:ℤ):ℝ)*u^3+(((0:ℤ):ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (10:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient10_0 p,cast_commonCoefficient10_1 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient11_0 (p : Params) : (commonCoefficient11_0 p:ℝ)=((-12000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((6000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient11_1 (p : Params) : (commonCoefficient11_1 p:ℝ)=((-24000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-24000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient11_2 (p : Params) : (commonCoefficient11_2 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-48000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-12000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((18000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient11_3 (p : Params) : (commonCoefficient11_3 p:ℝ)=((-48000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-72000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((24000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-24000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((24000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient11_4 (p : Params) : (commonCoefficient11_4 p:ℝ)=((-60000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-96000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((30000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((30000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient11_5 (p : Params) : (commonCoefficient11_5 p:ℝ)=((-72000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-120000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((36000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-48000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((36000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient11_6 (p : Params) : (commonCoefficient11_6 p:ℝ)=((-84000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-144000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((42000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-60000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((42000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient11_7 (p : Params) : (commonCoefficient11_7 p:ℝ)=((-168000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-72000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((48000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient11_8 (p : Params) : (commonCoefficient11_8 p:ℝ)=((-84000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower11 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (11:Fin 20) j).evalR) u=commonGate p.toReal (11:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (11:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (11:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (11:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient11_0 p:ℝ)*u^0+((commonCoefficient11_1 p:ℝ)*u^1+((commonCoefficient11_2 p:ℝ)*u^2+((commonCoefficient11_3 p:ℝ)*u^3+((commonCoefficient11_4 p:ℝ)*u^4+((commonCoefficient11_5 p:ℝ)*u^5+((commonCoefficient11_6 p:ℝ)*u^6+((commonCoefficient11_7 p:ℝ)*u^7+((commonCoefficient11_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (11:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient11_0 p,cast_commonCoefficient11_1 p,cast_commonCoefficient11_2 p,cast_commonCoefficient11_3 p,cast_commonCoefficient11_4 p,cast_commonCoefficient11_5 p,cast_commonCoefficient11_6 p,cast_commonCoefficient11_7 p,cast_commonCoefficient11_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient12_0 (p : Params) : (commonCoefficient12_0 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((-3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient12_1 (p : Params) : (commonCoefficient12_1 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((18000000000:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient12_2 (p : Params) : (commonCoefficient12_2 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient12_3 (p : Params) : (commonCoefficient12_3 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient12_4 (p : Params) : (commonCoefficient12_4 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient12_5 (p : Params) : (commonCoefficient12_5 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient12_6 (p : Params) : (commonCoefficient12_6 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient12_7 (p : Params) : (commonCoefficient12_7 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient12_8 (p : Params) : (commonCoefficient12_8 p:ℝ)=((-36000000000:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower12 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (12:Fin 20) j).evalR) u=commonGate p.toReal (12:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (12:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (12:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (12:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient12_0 p:ℝ)*u^0+((commonCoefficient12_1 p:ℝ)*u^1+((commonCoefficient12_2 p:ℝ)*u^2+((commonCoefficient12_3 p:ℝ)*u^3+((commonCoefficient12_4 p:ℝ)*u^4+((commonCoefficient12_5 p:ℝ)*u^5+((commonCoefficient12_6 p:ℝ)*u^6+((commonCoefficient12_7 p:ℝ)*u^7+((commonCoefficient12_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (12:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient12_0 p,cast_commonCoefficient12_1 p,cast_commonCoefficient12_2 p,cast_commonCoefficient12_3 p,cast_commonCoefficient12_4 p,cast_commonCoefficient12_5 p,cast_commonCoefficient12_6 p,cast_commonCoefficient12_7 p,cast_commonCoefficient12_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient13_0 (p : Params) : (commonCoefficient13_0 p:ℝ)=((-20400000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((7500000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((7500000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-4500000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient13_1 (p : Params) : (commonCoefficient13_1 p:ℝ)=((-40800000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-40800000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient13_2 (p : Params) : (commonCoefficient13_2 p:ℝ)=((-61200000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-81600000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((22500000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-20400000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((22500000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient13_3 (p : Params) : (commonCoefficient13_3 p:ℝ)=((-81600000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-122400000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((30000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-40800000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((30000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient13_4 (p : Params) : (commonCoefficient13_4 p:ℝ)=((-102000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-163200000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((37500000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-61200000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((37500000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient13_5 (p : Params) : (commonCoefficient13_5 p:ℝ)=((-122400000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-204000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((45000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-81600000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((45000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient13_6 (p : Params) : (commonCoefficient13_6 p:ℝ)=((-142800000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-244800000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((52500000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-102000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((52500000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient13_7 (p : Params) : (commonCoefficient13_7 p:ℝ)=((-285600000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-122400000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((60000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient13_8 (p : Params) : (commonCoefficient13_8 p:ℝ)=((-142800000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower13 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (13:Fin 20) j).evalR) u=commonGate p.toReal (13:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (13:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (13:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (13:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient13_0 p:ℝ)*u^0+((commonCoefficient13_1 p:ℝ)*u^1+((commonCoefficient13_2 p:ℝ)*u^2+((commonCoefficient13_3 p:ℝ)*u^3+((commonCoefficient13_4 p:ℝ)*u^4+((commonCoefficient13_5 p:ℝ)*u^5+((commonCoefficient13_6 p:ℝ)*u^6+((commonCoefficient13_7 p:ℝ)*u^7+((commonCoefficient13_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (13:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient13_0 p,cast_commonCoefficient13_1 p,cast_commonCoefficient13_2 p,cast_commonCoefficient13_3 p,cast_commonCoefficient13_4 p,cast_commonCoefficient13_5 p,cast_commonCoefficient13_6 p,cast_commonCoefficient13_7 p,cast_commonCoefficient13_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient14_0 (p : Params) : (commonCoefficient14_0 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^4) + ((27000000000:ℝ)*(p.q0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((-4500000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-4500000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient14_1 (p : Params) : (commonCoefficient14_1 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((27000000000:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^5) + ((-4500000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient14_2 (p : Params) : (commonCoefficient14_2 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient14_3 (p : Params) : (commonCoefficient14_3 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient14_4 (p : Params) : (commonCoefficient14_4 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient14_5 (p : Params) : (commonCoefficient14_5 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient14_6 (p : Params) : (commonCoefficient14_6 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient14_7 (p : Params) : (commonCoefficient14_7 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((27900000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient14_8 (p : Params) : (commonCoefficient14_8 p:ℝ)=((-45000000000:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((27900000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower14 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (14:Fin 20) j).evalR) u=commonGate p.toReal (14:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (14:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (14:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (14:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient14_0 p:ℝ)*u^0+((commonCoefficient14_1 p:ℝ)*u^1+((commonCoefficient14_2 p:ℝ)*u^2+((commonCoefficient14_3 p:ℝ)*u^3+((commonCoefficient14_4 p:ℝ)*u^4+((commonCoefficient14_5 p:ℝ)*u^5+((commonCoefficient14_6 p:ℝ)*u^6+((commonCoefficient14_7 p:ℝ)*u^7+((commonCoefficient14_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (14:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient14_0 p,cast_commonCoefficient14_1 p,cast_commonCoefficient14_2 p,cast_commonCoefficient14_3 p,cast_commonCoefficient14_4 p,cast_commonCoefficient14_5 p,cast_commonCoefficient14_6 p,cast_commonCoefficient14_7 p,cast_commonCoefficient14_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient15_0 (p : Params) : (commonCoefficient15_0 p:ℝ)=((-15000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((3000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient15_1 (p : Params) : (commonCoefficient15_1 p:ℝ)=((-30000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-30000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient15_2 (p : Params) : (commonCoefficient15_2 p:ℝ)=((-45000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-60000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((9000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-15000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((9000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient15_3 (p : Params) : (commonCoefficient15_3 p:ℝ)=((-60000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-90000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-30000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((12000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient15_4 (p : Params) : (commonCoefficient15_4 p:ℝ)=((-75000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-120000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-45000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((15000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient15_5 (p : Params) : (commonCoefficient15_5 p:ℝ)=((-90000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-150000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-60000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((18000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient15_6 (p : Params) : (commonCoefficient15_6 p:ℝ)=((-105000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-180000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((21000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-75000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((21000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient15_7 (p : Params) : (commonCoefficient15_7 p:ℝ)=((-210000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-90000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((24000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient15_8 (p : Params) : (commonCoefficient15_8 p:ℝ)=((-105000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower15 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (15:Fin 20) j).evalR) u=commonGate p.toReal (15:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (15:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (15:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (15:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient15_0 p:ℝ)*u^0+((commonCoefficient15_1 p:ℝ)*u^1+((commonCoefficient15_2 p:ℝ)*u^2+((commonCoefficient15_3 p:ℝ)*u^3+((commonCoefficient15_4 p:ℝ)*u^4+((commonCoefficient15_5 p:ℝ)*u^5+((commonCoefficient15_6 p:ℝ)*u^6+((commonCoefficient15_7 p:ℝ)*u^7+((commonCoefficient15_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (15:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient15_0 p,cast_commonCoefficient15_1 p,cast_commonCoefficient15_2 p,cast_commonCoefficient15_3 p,cast_commonCoefficient15_4 p,cast_commonCoefficient15_5 p,cast_commonCoefficient15_6 p,cast_commonCoefficient15_7 p,cast_commonCoefficient15_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient16_0 (p : Params) : (commonCoefficient16_0 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((-3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient16_1 (p : Params) : (commonCoefficient16_1 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y0:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((18000000000:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient16_2 (p : Params) : (commonCoefficient16_2 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y1:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient16_3 (p : Params) : (commonCoefficient16_3 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y2:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient16_4 (p : Params) : (commonCoefficient16_4 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y3:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient16_5 (p : Params) : (commonCoefficient16_5 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y4:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient16_6 (p : Params) : (commonCoefficient16_6 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y5:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient16_7 (p : Params) : (commonCoefficient16_7 p:ℝ)=((-18000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.y6:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient16_8 (p : Params) : (commonCoefficient16_8 p:ℝ)=((-18000000000:ℝ)*(p.y7:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower16 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (16:Fin 20) j).evalR) u=commonGate p.toReal (16:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (16:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (16:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (16:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient16_0 p:ℝ)*u^0+((commonCoefficient16_1 p:ℝ)*u^1+((commonCoefficient16_2 p:ℝ)*u^2+((commonCoefficient16_3 p:ℝ)*u^3+((commonCoefficient16_4 p:ℝ)*u^4+((commonCoefficient16_5 p:ℝ)*u^5+((commonCoefficient16_6 p:ℝ)*u^6+((commonCoefficient16_7 p:ℝ)*u^7+((commonCoefficient16_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (16:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient16_0 p,cast_commonCoefficient16_1 p,cast_commonCoefficient16_2 p,cast_commonCoefficient16_3 p,cast_commonCoefficient16_4 p,cast_commonCoefficient16_5 p,cast_commonCoefficient16_6 p,cast_commonCoefficient16_7 p,cast_commonCoefficient16_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient17_0 (p : Params) : (commonCoefficient17_0 p:ℝ)=((-6000000000:ℝ)*(p.cap:ℝ)*(p.den:ℝ)^5) + ((1000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

theorem eval_commonPower17 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (17:Fin 20) j).evalR) u=commonGate p.toReal (17:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (17:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (17:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (17:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient17_0 p:ℝ)*u^0+(((0:ℤ):ℝ)*u^1+(((0:ℤ):ℝ)*u^2+(((0:ℤ):ℝ)*u^3+(((0:ℤ):ℝ)*u^4+(((0:ℤ):ℝ)*u^5+(((0:ℤ):ℝ)*u^6+(((0:ℤ):ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (17:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient17_0 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient18_0 (p : Params) : (commonCoefficient18_0 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient18_1 (p : Params) : (commonCoefficient18_1 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-16200000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient18_2 (p : Params) : (commonCoefficient18_2 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-16200000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient18_3 (p : Params) : (commonCoefficient18_3 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-16200000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient18_4 (p : Params) : (commonCoefficient18_4 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-16200000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient18_5 (p : Params) : (commonCoefficient18_5 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-16200000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient18_6 (p : Params) : (commonCoefficient18_6 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-16200000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient18_7 (p : Params) : (commonCoefficient18_7 p:ℝ)=((-16200000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-16200000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient18_8 (p : Params) : (commonCoefficient18_8 p:ℝ)=((-16200000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower18 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (18:Fin 20) j).evalR) u=commonGate p.toReal (18:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (18:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (18:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (18:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient18_0 p:ℝ)*u^0+((commonCoefficient18_1 p:ℝ)*u^1+((commonCoefficient18_2 p:ℝ)*u^2+((commonCoefficient18_3 p:ℝ)*u^3+((commonCoefficient18_4 p:ℝ)*u^4+((commonCoefficient18_5 p:ℝ)*u^5+((commonCoefficient18_6 p:ℝ)*u^6+((commonCoefficient18_7 p:ℝ)*u^7+((commonCoefficient18_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (18:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient18_0 p,cast_commonCoefficient18_1 p,cast_commonCoefficient18_2 p,cast_commonCoefficient18_3 p,cast_commonCoefficient18_4 p,cast_commonCoefficient18_5 p,cast_commonCoefficient18_6 p,cast_commonCoefficient18_7 p,cast_commonCoefficient18_8 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
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

private theorem cast_commonCoefficient19_0 (p : Params) : (commonCoefficient19_0 p:ℝ)=((-4500000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_commonCoefficient19_1 (p : Params) : (commonCoefficient19_1 p:ℝ)=((-4500000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient19_2 (p : Params) : (commonCoefficient19_2 p:ℝ)=((-4500000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient19_3 (p : Params) : (commonCoefficient19_3 p:ℝ)=((-4500000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient19_4 (p : Params) : (commonCoefficient19_4 p:ℝ)=((-4500000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient19_5 (p : Params) : (commonCoefficient19_5 p:ℝ)=((-4500000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient19_6 (p : Params) : (commonCoefficient19_6 p:ℝ)=((-4500000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_commonCoefficient19_7 (p : Params) : (commonCoefficient19_7 p:ℝ)=((-4500000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_commonPower19 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(commonPower p (19:Fin 20) j).evalR) u=commonGate p.toReal (19:Fin 20) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(commonPower p (19:Fin 20) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(commonNumerator p (19:Fin 20) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (commonNumerator p (19:Fin 20)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((commonCoefficient19_0 p:ℝ)*u^0+((commonCoefficient19_1 p:ℝ)*u^1+((commonCoefficient19_2 p:ℝ)*u^2+((commonCoefficient19_3 p:ℝ)*u^3+((commonCoefficient19_4 p:ℝ)*u^4+((commonCoefficient19_5 p:ℝ)*u^5+((commonCoefficient19_6 p:ℝ)*u^6+((commonCoefficient19_7 p:ℝ)*u^7+(((0:ℤ):ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = commonGate p.toReal (19:Fin 20) u*(denominator p:ℝ)
 rw [cast_commonCoefficient19_0 p,cast_commonCoefficient19_1 p,cast_commonCoefficient19_2 p,cast_commonCoefficient19_3 p,cast_commonCoefficient19_4 p,cast_commonCoefficient19_5 p,cast_commonCoefficient19_6 p,cast_commonCoefficient19_7 p]
 norm_num [denominator,scale,order,commonGate,Params.toReal]
 field_simp [hd]
 ring
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
