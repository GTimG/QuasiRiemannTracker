/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row196_coefficients : Fin 3 → Fin 4 → ℝ := ![![(27073967662676775187654688069/46011787588325478515625:ℝ),(68578895417228942663150337983/46011787588325478515625:ℝ),(56318257356699993264296401459/46011787588325478515625:ℝ),(2962665920429565157760150309/9202357517665095703125:ℝ)],
![(49743783083945286476449130266/46011787588325478515625:ℝ),(122251631566413464018342588062/46011787588325478515625:ℝ),(96068663703373835083353504026/46011787588325478515625:ℝ),(4712163044181131508292009246/9202357517665095703125:ℝ)],
![(25853071505020691415502540697/46011787588325478515625:ℝ),(889373677764116183694058849/648053346314443359375:ℝ),(49146826264623157297773708892/46011787588325478515625:ℝ),(2370873329678319934199614262/9202357517665095703125:ℝ)]]
theorem row196_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (2356081522090565754146004623/4391536064941258702848000000000:ℝ) row196_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row196_coefficients,Fin.sum_univ_succ]
 ring
theorem row196_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row196_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row196_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row196_pos
