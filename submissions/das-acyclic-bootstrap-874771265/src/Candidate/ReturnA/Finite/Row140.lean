/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row140_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5580440660971277969401254079/116592790160485070156250000:ℝ),(88790110150600906964480374091/1049335111444365631406250000:ℝ),(22536944172498333677666036237/524667555722182815703125000:ℝ),(2616243083615684221168992547/524667555722182815703125000:ℝ)],
![(3953792056660903569670383757/29148197540121267539062500:ℝ),(65487401882820207971151036547/262333777861091407851562500:ℝ),(7212108903260283028913768071/52466755572218281570312500:ℝ),(5307099159492076851701257621/262333777861091407851562500:ℝ)],
![(2116916210201294680063629679/19432131693414178359375000:ℝ),(115090786544192058152505181711/524667555722182815703125000:ℝ),(74132527130076427797541872023/524667555722182815703125000:ℝ),(3012983123213928548350938329/104933511144436563140625000:ℝ)]]
theorem row140_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2616243083615684221168992547/955128136994693694720000000000:ℝ) row140_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row140_coefficients,Fin.sum_univ_succ]
 ring
theorem row140_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row140_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row140_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row140_pos
