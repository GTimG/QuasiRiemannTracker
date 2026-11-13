/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row109_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20178433593543152124705389761/5246675557221828157031250:ℝ),(1339049454632004347287006181611/131166888930545703925781250:ℝ),(1180615220684455022102117597747/131166888930545703925781250:ℝ),(345743215229717057116496160161/131166888930545703925781250:ℝ)],
![(410669258351946670089963943729/65583444465272851962890625:ℝ),(205595162229895723526032792511/13116688893054570392578125:ℝ),(843272883954330625791491938673/65583444465272851962890625:ℝ),(225612092830158152230979419847/65583444465272851962890625:ℝ)],
![(459331365134183823278276001883/131166888930545703925781250:ℝ),(1128200067142055772983590546399/131166888930545703925781250:ℝ),(1803773414643616103516830814923/262333777861091407851562500:ℝ),(465150414811270889055420475891/262333777861091407851562500:ℝ)]]
theorem row109_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (225612092830158152230979419847/61128200767660396462080000000000:ℝ) row109_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row109_coefficients,Fin.sum_univ_succ]
 ring
theorem row109_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row109_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row109_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row109_pos
