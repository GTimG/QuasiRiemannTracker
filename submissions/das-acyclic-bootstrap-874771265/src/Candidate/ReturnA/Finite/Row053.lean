/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row053_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8311725068044267561599149674532006296507/62290817814981411632812500000:ℝ),(74432092732547463146206776233728512133937/186872453444944234898437500000:ℝ),(28572320594866192317788735684779054272/72095853952524781982421875:ℝ),(767579275051468662762433271791087982144/5839764170154507340576171875:ℝ)],
![(9891614915293230376639260323680585930411/37374490688988846979687500000:ℝ),(29525745999629150448209284121469351087787/37374490688988846979687500000:ℝ),(918030194275403640051870486232203524992/1167952834030901468115234375:ℝ),(304463589689103825577102071848179613824/1167952834030901468115234375:ℝ)],
![(3923849319476250748240164265544726890889/29899592551191077583750000000:ℝ),(780801179896952075424872239318271098087/1993306170079405172250000000:ℝ),(91036057718186286477344169844641530048/233590566806180293623046875:ℝ),(1437666258667380789459501684666955456/11123360324103823505859375:ℝ)]]
theorem row053_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (22463535291677824835304713822921179/339729556008176941982023680000000000:ℝ) row053_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row053_coefficients,Fin.sum_univ_succ]
 ring
theorem row053_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row053_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row053_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row053_pos
