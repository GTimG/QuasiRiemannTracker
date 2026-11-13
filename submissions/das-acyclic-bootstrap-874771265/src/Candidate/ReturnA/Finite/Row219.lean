/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row219_coefficients : Fin 3 → Fin 4 → ℝ := ![![(468047603072185168775233445470680115328/72510858943824723899720291015625:ℝ),(1115901411131148860738981415565962310784/72510858943824723899720291015625:ℝ),(11738269359605389952242266640818274304/1021279703434151040841130859375:ℝ),(185540995823311221729188190152815280128/72510858943824723899720291015625:ℝ)],
![(4950892436749005772778883336851136167456/362554294719123619498601455078125:ℝ),(11885333342949655469584303962626717628704/362554294719123619498601455078125:ℝ),(256484234479397635254685098135704428544/10358694134832103414245755859375:ℝ),(2042278513918762864716843903661573537792/362554294719123619498601455078125:ℝ)],
![(38734431643851679709593040394242710646/5106398517170755204205654296875:ℝ),(6721805784730872123029247681333759841834/362554294719123619498601455078125:ℝ),(1044673520989993738940403813208828009984/72510858943824723899720291015625:ℝ),(1251589213769569686453123876228956413952/362554294719123619498601455078125:ℝ)]]
theorem row219_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (707782729428524863163712273226987/4224063690437775204881839104000000000:ℝ) row219_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row219_coefficients,Fin.sum_univ_succ]
 ring
theorem row219_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row219_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row219_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row219_pos
