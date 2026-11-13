/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row196_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18048882309949335544752731503/30674520519075175781250:ℝ),(15239328494921558396180666207/10224840173025058593750:ℝ),(4171581893644033919295028337/3408280057675019531250:ℝ),(1975026773596193125973197583/6134904103815035156250:ℝ)],
![(16580848043382964426234784071/15337260259537587890625:ℝ),(4527701689948777329285415333/1704140028837509765625:ℝ),(32021669559080745556547855431/15337260259537587890625:ℝ),(1570640478584942803842780301/3067452051907517578125:ℝ)],
![(17234984004061742128773948139/30674520519075175781250:ℝ),(14031946699817566928632800391/10224840173025058593750:ℝ),(16381690270303336624405757002/15337260259537587890625:ℝ),(263417481507190486389568699/1022484017302505859375:ℝ)]]
theorem row196_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (1570640478584942803842780301/2927690276664640536576000000000:ℝ) row196_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row196_coefficients,Fin.sum_univ_succ]
 ring
theorem row196_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row196_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row196_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row196_pos
