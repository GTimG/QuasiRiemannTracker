/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row044_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12303993564647398581431940009767/7905331476562500000000:ℝ),(4405730812131428389154008571293/948639777187500000000:ℝ),(219103781795598993243484547056283/47431988859375000000000:ℝ),(4842746838460797684958383903349/3162132590625000000000:ℝ)],
![(35794890635238664661640432626359/11857997214843750000000:ℝ),(21358405527537090760126588704709/2371599442968750000000:ℝ),(3318771918741159475807335179903/370562412963867187500:ℝ),(1173452146575677136228073828657/395266573828125000000:ℝ)],
![(34701685148720101048926815790611/23715994429687500000000:ℝ),(1380166003766742979612904515603/316213259062500000000:ℝ),(102921189248759063293124804544019/23715994429687500000000:ℝ),(2274028274331562724738918777627/1581066295312500000000:ℝ)]]
theorem row044_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (2274028274331562724738918777627/24144455221955788800000000000000:ℝ) row044_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row044_coefficients,Fin.sum_univ_succ]
 ring
theorem row044_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row044_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row044_pos
