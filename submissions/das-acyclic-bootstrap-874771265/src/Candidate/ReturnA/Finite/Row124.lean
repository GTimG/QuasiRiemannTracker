/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row124_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7128572811456098173286536711278017369/1532107964309842402998046875:ℝ),(62818576957642227222653048478742462651/4596323892929527208994140625:ℝ),(61491344019677154102382247726500345856/4596323892929527208994140625:ℝ),(20058464219963727552994714362060685312/4596323892929527208994140625:ℝ)],
![(328517075975787614821836642630528184/35630417774647497744140625:ℝ),(124444959032255250603006812588713092152/4596323892929527208994140625:ℝ),(17396662283661053708765810393125961728/656617698989932458427734375:ℝ),(7942067385367007366154986256251355136/919264778585905441798828125:ℝ)],
![(7002518339481819735634386659548970768/1532107964309842402998046875:ℝ),(61669970503320784624204762205917769776/4596323892929527208994140625:ℝ),(1723678779130597064953741560155766784/131323539797986491685546875:ℝ),(2809474318976539863782325223668711424/656617698989932458427734375:ℝ)]]
theorem row124_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (21434588004886931333788492001867/9792192858112958827069440000000000:ℝ) row124_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row124_coefficients,Fin.sum_univ_succ]
 ring
theorem row124_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row124_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row124_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row124_pos
