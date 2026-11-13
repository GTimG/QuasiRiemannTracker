/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row164_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2074613050054159945715448186974868361658/35456788924465510711669921875:ℝ),(37451792930430448563276843756273793733707/319111100320189596405029296875:ℝ),(18937871913392842566255310139655639491072/319111100320189596405029296875:ℝ),(157572507868389861877350256635548902912/319111100320189596405029296875:ℝ)],
![(661480987258429982288420648887199268931/5673086227914481713867187500:ℝ),(119086308058543529111621289053129642858633/510577760512303354248046875000:ℝ),(7466159267653368414405101356864546999808/63822220064037919281005859375:ℝ),(22022281423275933352561223313262861312/63822220064037919281005859375:ℝ)],
![(16928790619673922791479249357794049573/290462014869221463750000000:ℝ),(121773166139750465371329808238746040423/1045663253529197269500000000:ℝ),(5944914319816056454764826654242522544/102115552102460670849609375:ℝ),(4523835465380985843423589133464064/102115552102460670849609375:ℝ)]]
theorem row164_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (8835616143322237975436697526297/399207953469943009211999846400000000000:ℝ) row164_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row164_coefficients,Fin.sum_univ_succ]
 ring
theorem row164_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row164_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row164_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row164_pos
