/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row079_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69487384872702304547256581/1166639487099609375:ℝ),(40485893471701910109547361/233327897419921875:ℝ),(392955774915052277705992459/2333278974199218750:ℝ),(42357203314479261901677337/777759658066406250:ℝ)],
![(134017534750850917111229902/1166639487099609375:ℝ),(5815716447552517717489478/17412529658203125:ℝ),(377418926216276363639010496/1166639487099609375:ℝ),(40594486327036197892815124/388879829033203125:ℝ)],
![(65181096700150758527245571/1166639487099609375:ℝ),(189169019661934140989553121/1166639487099609375:ℝ),(182879198623452998205368579/1166639487099609375:ℝ),(19630425220556538581020343/388879829033203125:ℝ)]]
theorem row079_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (19630425220556538581020343/5938581858743746560000000000:ℝ) row079_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row079_coefficients,Fin.sum_univ_succ]
 ring
theorem row079_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row079_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row079_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row079_pos
