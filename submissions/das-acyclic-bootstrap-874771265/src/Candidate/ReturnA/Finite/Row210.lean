/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row210_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8980534493197757398067254494678921538024/362554294719123619498601455078125:ℝ),(21506530749501492716826738509204298684328/362554294719123619498601455078125:ℝ),(16181116191810490958497989545633133737984/362554294719123619498601455078125:ℝ),(730939112830837321433604313543426318336/72510858943824723899720291015625:ℝ)],
![(717757635885930625770961908786901025768/14502171788764944779944058203125:ℝ),(42801781972531475329483053446195371342184/362554294719123619498601455078125:ℝ),(4570538031887900439614819453666248321024/51793470674160517071228779296875:ℝ),(7135065523810222787657083446375267549184/362554294719123619498601455078125:ℝ)],
![(9102896629275897576685182983487100971226/362554294719123619498601455078125:ℝ),(21711230720466943569796165733527926424906/362554294719123619498601455078125:ℝ),(2318022150319396716091398845545082419712/51793470674160517071228779296875:ℝ),(3617385638623399110871282801989595234304/362554294719123619498601455078125:ℝ)]]
theorem row210_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (435489839099745043191960659568802951/2703400761880176131124377026560000000000:ℝ) row210_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row210_coefficients,Fin.sum_univ_succ]
 ring
theorem row210_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row210_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row210_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row210_pos
