/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row127_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8616520682135353981113338286558742201/1838529557171810883597656250:ℝ),(126437319120852893151918366015700393079/9192647785859054417988281250:ℝ),(123650471761562457457232516378297434543/9192647785859054417988281250:ℝ),(40295711835358402940422986389140752469/9192647785859054417988281250:ℝ)],
![(42792165297210529657582851011928458093/4596323892929527208994140625:ℝ),(125550994257135620040976094893684149527/4596323892929527208994140625:ℝ),(4909971005396904976042496305381937899/183852955717181088359765625:ℝ),(39990401679121324701195752299667756041/4596323892929527208994140625:ℝ)],
![(42531116347630384214942516261083367381/9192647785859054417988281250:ℝ),(199604141147982786819089816447455319/14708236457374487068781250:ℝ),(121935749474113085834140421256619123957/9192647785859054417988281250:ℝ),(39714232826758549291460204636480416963/9192647785859054417988281250:ℝ)]]
theorem row127_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (39714232826758549291460204636480416963/17968752232180144351343038955520000000000:ℝ) row127_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row127_coefficients,Fin.sum_univ_succ]
 ring
theorem row127_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row127_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row127_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row127_pos
