/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/


/- Cheap gate identities grouped without changing their theorem bodies. -/

import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveHigherIntegerEvalCore

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open FractionArithmetic

private theorem cast_pureCoefficient0_0 (p : Params) : (pureCoefficient0_0 p:ℝ)=((-12000000000:ℝ)*(p.q0:ℝ)^3*(p.y1:ℝ)*(p.den:ℝ)^2) + ((12000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((1000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((6000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^4) + ((-6000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-5000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-1500000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((-6000000000:ℝ)*(p.y0:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-5000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((1500000000:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^5) + ((-1250000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_pureCoefficient0_1 (p : Params) : (pureCoefficient0_1 p:ℝ)=((-24000000000:ℝ)*(p.q0:ℝ)^3*(p.y2:ℝ)*(p.den:ℝ)^2) + ((-36000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((24000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((2000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((24000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((8000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-12000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-10000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-12000000000:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-10000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((-1500000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_pureCoefficient0_2 (p : Params) : (pureCoefficient0_2 p:ℝ)=((-36000000000:ℝ)*(p.q0:ℝ)^3*(p.y3:ℝ)*(p.den:ℝ)^2) + ((-72000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((36000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((3000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-36000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((48000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((10000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-18000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-15000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((7000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((-18000000000:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-15000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient0_3 (p : Params) : (pureCoefficient0_3 p:ℝ)=((-48000000000:ℝ)*(p.q0:ℝ)^3*(p.y4:ℝ)*(p.den:ℝ)^2) + ((-108000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((48000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((4000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-72000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((72000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((12000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-24000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-20000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-12000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((24000000000:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((8000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((-24000000000:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-20000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient0_4 (p : Params) : (pureCoefficient0_4 p:ℝ)=((-60000000000:ℝ)*(p.q0:ℝ)^3*(p.y5:ℝ)*(p.den:ℝ)^2) + ((-144000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((60000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((5000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-108000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((96000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((14000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-30000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-25000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-24000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((36000000000:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((9000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((-30000000000:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-25000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient0_5 (p : Params) : (pureCoefficient0_5 p:ℝ)=((-72000000000:ℝ)*(p.q0:ℝ)^3*(p.y6:ℝ)*(p.den:ℝ)^2) + ((-180000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((72000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((6000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-144000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((120000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((16000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-30000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-36000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((48000000000:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((10000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((-36000000000:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-30000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient0_6 (p : Params) : (pureCoefficient0_6 p:ℝ)=((-84000000000:ℝ)*(p.q0:ℝ)^3*(p.y7:ℝ)*(p.den:ℝ)^2) + ((-216000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((84000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((7000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-180000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((144000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-42000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-35000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-48000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((60000000000:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((11000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((-42000000000:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-35000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient0_7 (p : Params) : (pureCoefficient0_7 p:ℝ)=((-252000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-216000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((168000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((20000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-60000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((72000000000:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((-48000000000:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-40000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient0_8 (p : Params) : (pureCoefficient0_8 p:ℝ)=((-252000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-72000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((84000000000:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((13000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient0_9 (p : Params) : (pureCoefficient0_9 p:ℝ)=((-84000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_purePower0 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(purePower p (0:Fin 4) j).evalR) u=pureGate p.toReal (0:Fin 4) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(purePower p (0:Fin 4) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(pureNumerator p (0:Fin 4) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (pureNumerator p (0:Fin 4)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((pureCoefficient0_0 p:ℝ)*u^0+((pureCoefficient0_1 p:ℝ)*u^1+((pureCoefficient0_2 p:ℝ)*u^2+((pureCoefficient0_3 p:ℝ)*u^3+((pureCoefficient0_4 p:ℝ)*u^4+((pureCoefficient0_5 p:ℝ)*u^5+((pureCoefficient0_6 p:ℝ)*u^6+((pureCoefficient0_7 p:ℝ)*u^7+((pureCoefficient0_8 p:ℝ)*u^8+((pureCoefficient0_9 p:ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = pureGate p.toReal (0:Fin 4) u*(denominator p:ℝ)
 rw [cast_pureCoefficient0_0 p,cast_pureCoefficient0_1 p,cast_pureCoefficient0_2 p,cast_pureCoefficient0_3 p,cast_pureCoefficient0_4 p,cast_pureCoefficient0_5 p,cast_pureCoefficient0_6 p,cast_pureCoefficient0_7 p,cast_pureCoefficient0_8 p,cast_pureCoefficient0_9 p]
 norm_num [denominator,scale,order,pureGate,Params.toReal]
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

private theorem cast_pureCoefficient1_0 (p : Params) : (pureCoefficient1_0 p:ℝ)=((15000000000:ℝ)*(p.q0:ℝ)^3*(p.y1:ℝ)*(p.den:ℝ)^2) + ((-15000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((-28000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((-3000000000:ℝ)*(p.q0:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^4) + ((3000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((5000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((4500000000:ℝ)*(p.q0:ℝ)*(p.den:ℝ)^5) + ((3000000000:ℝ)*(p.y0:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((5000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-4500000000:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^5) + ((-6250000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_pureCoefficient1_1 (p : Params) : (pureCoefficient1_1 p:ℝ)=((30000000000:ℝ)*(p.q0:ℝ)^3*(p.y2:ℝ)*(p.den:ℝ)^2) + ((45000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((-30000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((-56000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-30000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-59000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((6000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((10000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-3000000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((6000000000:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((10000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((4500000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_pureCoefficient1_2 (p : Params) : (pureCoefficient1_2 p:ℝ)=((45000000000:ℝ)*(p.q0:ℝ)^3*(p.y3:ℝ)*(p.den:ℝ)^2) + ((90000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-45000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((-84000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((45000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-60000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-115000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((9000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((15000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-15000000000:ℝ)*(p.y1:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-31000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((9000000000:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient1_3 (p : Params) : (pureCoefficient1_3 p:ℝ)=((60000000000:ℝ)*(p.q0:ℝ)^3*(p.y4:ℝ)*(p.den:ℝ)^2) + ((135000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-60000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((-112000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((90000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-90000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-171000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((12000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((20000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((-30000000000:ℝ)*(p.y2:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-59000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((12000000000:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((20000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient1_4 (p : Params) : (pureCoefficient1_4 p:ℝ)=((75000000000:ℝ)*(p.q0:ℝ)^3*(p.y5:ℝ)*(p.den:ℝ)^2) + ((180000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-75000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((-140000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((135000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-120000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-227000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((15000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((25000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((30000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((-45000000000:ℝ)*(p.y3:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-87000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((15000000000:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((25000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient1_5 (p : Params) : (pureCoefficient1_5 p:ℝ)=((90000000000:ℝ)*(p.q0:ℝ)^3*(p.y6:ℝ)*(p.den:ℝ)^2) + ((225000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-90000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((-168000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((180000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-150000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-283000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((18000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((30000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((45000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((-60000000000:ℝ)*(p.y4:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-115000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((18000000000:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((30000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient1_6 (p : Params) : (pureCoefficient1_6 p:ℝ)=((105000000000:ℝ)*(p.q0:ℝ)^3*(p.y7:ℝ)*(p.den:ℝ)^2) + ((270000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-105000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^2) + ((-196000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((225000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-180000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-339000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((21000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((35000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((60000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((-75000000000:ℝ)*(p.y5:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-143000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((21000000000:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((35000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient1_7 (p : Params) : (pureCoefficient1_7 p:ℝ)=((315000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((270000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-210000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^3) + ((-395000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((75000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((-90000000000:ℝ)*(p.y6:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-171000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((24000000000:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((40000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient1_8 (p : Params) : (pureCoefficient1_8 p:ℝ)=((315000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((90000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((-105000000000:ℝ)*(p.y7:ℝ)*(p.eps:ℝ)*(p.den:ℝ)^4) + ((-199000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient1_9 (p : Params) : (pureCoefficient1_9 p:ℝ)=((105000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_purePower1 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(purePower p (1:Fin 4) j).evalR) u=pureGate p.toReal (1:Fin 4) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(purePower p (1:Fin 4) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(pureNumerator p (1:Fin 4) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (pureNumerator p (1:Fin 4)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((pureCoefficient1_0 p:ℝ)*u^0+((pureCoefficient1_1 p:ℝ)*u^1+((pureCoefficient1_2 p:ℝ)*u^2+((pureCoefficient1_3 p:ℝ)*u^3+((pureCoefficient1_4 p:ℝ)*u^4+((pureCoefficient1_5 p:ℝ)*u^5+((pureCoefficient1_6 p:ℝ)*u^6+((pureCoefficient1_7 p:ℝ)*u^7+((pureCoefficient1_8 p:ℝ)*u^8+((pureCoefficient1_9 p:ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = pureGate p.toReal (1:Fin 4) u*(denominator p:ℝ)
 rw [cast_pureCoefficient1_0 p,cast_pureCoefficient1_1 p,cast_pureCoefficient1_2 p,cast_pureCoefficient1_3 p,cast_pureCoefficient1_4 p,cast_pureCoefficient1_5 p,cast_pureCoefficient1_6 p,cast_pureCoefficient1_7 p,cast_pureCoefficient1_8 p,cast_pureCoefficient1_9 p]
 norm_num [denominator,scale,order,pureGate,Params.toReal]
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

private theorem cast_pureCoefficient2_0 (p : Params) : (pureCoefficient2_0 p:ℝ)=((-14000000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((-500000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-500000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-2375000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_pureCoefficient2_1 (p : Params) : (pureCoefficient2_1 p:ℝ)=((-28000000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-28000000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((-1000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-1000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient2_2 (p : Params) : (pureCoefficient2_2 p:ℝ)=((-42000000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-56000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((-1500000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-14000000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((-1500000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient2_3 (p : Params) : (pureCoefficient2_3 p:ℝ)=((-56000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-84000000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-2000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-28000000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((-2000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient2_4 (p : Params) : (pureCoefficient2_4 p:ℝ)=((-70000000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-112000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-2500000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-42000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((-2500000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient2_5 (p : Params) : (pureCoefficient2_5 p:ℝ)=((-84000000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-140000000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-3000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-56000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((-3000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient2_6 (p : Params) : (pureCoefficient2_6 p:ℝ)=((-98000000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-168000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-3500000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-70000000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((-3500000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient2_7 (p : Params) : (pureCoefficient2_7 p:ℝ)=((-196000000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-84000000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((-4000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient2_8 (p : Params) : (pureCoefficient2_8 p:ℝ)=((-98000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_purePower2 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(purePower p (2:Fin 4) j).evalR) u=pureGate p.toReal (2:Fin 4) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(purePower p (2:Fin 4) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(pureNumerator p (2:Fin 4) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (pureNumerator p (2:Fin 4)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((pureCoefficient2_0 p:ℝ)*u^0+((pureCoefficient2_1 p:ℝ)*u^1+((pureCoefficient2_2 p:ℝ)*u^2+((pureCoefficient2_3 p:ℝ)*u^3+((pureCoefficient2_4 p:ℝ)*u^4+((pureCoefficient2_5 p:ℝ)*u^5+((pureCoefficient2_6 p:ℝ)*u^6+((pureCoefficient2_7 p:ℝ)*u^7+((pureCoefficient2_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = pureGate p.toReal (2:Fin 4) u*(denominator p:ℝ)
 rw [cast_pureCoefficient2_0 p,cast_pureCoefficient2_1 p,cast_pureCoefficient2_2 p,cast_pureCoefficient2_3 p,cast_pureCoefficient2_4 p,cast_pureCoefficient2_5 p,cast_pureCoefficient2_6 p,cast_pureCoefficient2_7 p,cast_pureCoefficient2_8 p]
 norm_num [denominator,scale,order,pureGate,Params.toReal]
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

private theorem cast_pureCoefficient3_0 (p : Params) : (pureCoefficient3_0 p:ℝ)=((-13750000000:ℝ)*(p.q0:ℝ)^2*(p.y1:ℝ)*(p.den:ℝ)^3) + ((2750000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((2750000000:ℝ)*(p.y0:ℝ)*(p.den:ℝ)^5) + ((-2875000000:ℝ)*(p.den:ℝ)^6) := by
 norm_cast

private theorem cast_pureCoefficient3_1 (p : Params) : (pureCoefficient3_1 p:ℝ)=((-27500000000:ℝ)*(p.q0:ℝ)^2*(p.y2:ℝ)*(p.den:ℝ)^3) + ((-27500000000:ℝ)*(p.q0:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^4) + ((5500000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((5500000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient3_2 (p : Params) : (pureCoefficient3_2 p:ℝ)=((-41250000000:ℝ)*(p.q0:ℝ)^2*(p.y3:ℝ)*(p.den:ℝ)^3) + ((-55000000000:ℝ)*(p.q0:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^4) + ((8250000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((-13750000000:ℝ)*(p.y1:ℝ)*(p.den:ℝ)^5) + ((8250000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient3_3 (p : Params) : (pureCoefficient3_3 p:ℝ)=((-55000000000:ℝ)*(p.q0:ℝ)^2*(p.y4:ℝ)*(p.den:ℝ)^3) + ((-82500000000:ℝ)*(p.q0:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^4) + ((11000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((-27500000000:ℝ)*(p.y2:ℝ)*(p.den:ℝ)^5) + ((11000000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient3_4 (p : Params) : (pureCoefficient3_4 p:ℝ)=((-68750000000:ℝ)*(p.q0:ℝ)^2*(p.y5:ℝ)*(p.den:ℝ)^3) + ((-110000000000:ℝ)*(p.q0:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^4) + ((13750000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((-41250000000:ℝ)*(p.y3:ℝ)*(p.den:ℝ)^5) + ((13750000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient3_5 (p : Params) : (pureCoefficient3_5 p:ℝ)=((-82500000000:ℝ)*(p.q0:ℝ)^2*(p.y6:ℝ)*(p.den:ℝ)^3) + ((-137500000000:ℝ)*(p.q0:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^4) + ((16500000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((-55000000000:ℝ)*(p.y4:ℝ)*(p.den:ℝ)^5) + ((16500000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient3_6 (p : Params) : (pureCoefficient3_6 p:ℝ)=((-96250000000:ℝ)*(p.q0:ℝ)^2*(p.y7:ℝ)*(p.den:ℝ)^3) + ((-165000000000:ℝ)*(p.q0:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^4) + ((19250000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-68750000000:ℝ)*(p.y5:ℝ)*(p.den:ℝ)^5) + ((19250000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient3_7 (p : Params) : (pureCoefficient3_7 p:ℝ)=((-192500000000:ℝ)*(p.q0:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^4) + ((-82500000000:ℝ)*(p.y6:ℝ)*(p.den:ℝ)^5) + ((22000000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

private theorem cast_pureCoefficient3_8 (p : Params) : (pureCoefficient3_8 p:ℝ)=((-96250000000:ℝ)*(p.y7:ℝ)*(p.den:ℝ)^5) := by
 norm_cast

theorem eval_purePower3 (p : Params) (u : ℝ) :
 SourceCurveHigherCertificate.eval (fun j=>(purePower p (3:Fin 4) j).evalR) u=pureGate p.toReal (3:Fin 4) u := by
 have hd : (p.den:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.den_pos)
 rw [show SourceCurveHigherCertificate.eval (fun j=>(purePower p (3:Fin 4) j).evalR) u=
   SourceCurveHigherCertificate.eval (fun j=>(pureNumerator p (3:Fin 4) j:ℝ)) u/(denominator p:ℝ) from
   eval_mk (pureNumerator p (3:Fin 4)) (denominator p) (denominator_pos p) u]
 apply (div_eq_iff (show (denominator p:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (denominator_pos p)))).2
 simp only [SourceCurveHigherCertificate.eval,Fin.sum_univ_succ,Fin.sum_univ_zero]
 change ((pureCoefficient3_0 p:ℝ)*u^0+((pureCoefficient3_1 p:ℝ)*u^1+((pureCoefficient3_2 p:ℝ)*u^2+((pureCoefficient3_3 p:ℝ)*u^3+((pureCoefficient3_4 p:ℝ)*u^4+((pureCoefficient3_5 p:ℝ)*u^5+((pureCoefficient3_6 p:ℝ)*u^6+((pureCoefficient3_7 p:ℝ)*u^7+((pureCoefficient3_8 p:ℝ)*u^8+(((0:ℤ):ℝ)*u^9+(((0:ℤ):ℝ)*u^10+(((0:ℤ):ℝ)*u^11+(((0:ℤ):ℝ)*u^12+(((0:ℤ):ℝ)*u^13+(((0:ℤ):ℝ)*u^14+(((0:ℤ):ℝ)*u^15+(0:ℝ))))))))))))))))) = pureGate p.toReal (3:Fin 4) u*(denominator p:ℝ)
 rw [cast_pureCoefficient3_0 p,cast_pureCoefficient3_1 p,cast_pureCoefficient3_2 p,cast_pureCoefficient3_3 p,cast_pureCoefficient3_4 p,cast_pureCoefficient3_5 p,cast_pureCoefficient3_6 p,cast_pureCoefficient3_7 p,cast_pureCoefficient3_8 p]
 norm_num [denominator,scale,order,pureGate,Params.toReal]
 field_simp [hd]
 ring
end
end Qrh.JointDetector.RepeatedMarks.SourceCurveHigherInteger
