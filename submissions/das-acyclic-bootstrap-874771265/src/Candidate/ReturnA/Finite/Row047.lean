/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row047_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3341629651377107837470434990161138565223/2989959255119107758375000000000:ℝ),(661977211084690031828322692217574473371/199330617007940517225000000000:ℝ),(9834823233928581671776502090294871808637/2989959255119107758375000000000:ℝ),(30921848419281669732269661878022793079/28475802429705788175000000000:ℝ)],
![(1078791108784353114958476914733393648733/498326542519851293062500000000:ℝ),(1922913583214308240266202648332099591601/298995925511910775837500000000:ℝ),(9520416358278639772281109863636580918361/1494979627559553879187500000000:ℝ),(29925915398462710805501888249297751491/14237901214852894087500000000:ℝ)],
![(3133454321587780677612881677631220856847/2989959255119107758375000000000:ℝ),(372259064964715369790968604510558397997/119598370204764310335000000000:ℝ),(9212995408924286640477100444107630491663/2989959255119107758375000000000:ℝ),(28952118452590876896574890085475156177/28475802429705788175000000000:ℝ)]]
theorem row047_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (28952118452590876896574890085475156177/434853831690466485736990310400000000000:ℝ) row047_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row047_coefficients,Fin.sum_univ_succ]
 ring
theorem row047_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row047_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row047_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row047_pos
