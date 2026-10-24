/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row117_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31667913254557908449909893697386919/735407006325009995039062500:ℝ),(91593965428325774320781012964656341/735407006325009995039062500:ℝ),(3529592959441930969744833962101253/29416280253000399801562500:ℝ),(304446959184888372069308297422171/7907602218548494570312500:ℝ)],
![(30569920625807481246689298786526679/367703503162504997519531250:ℝ),(3529188059391923753914537575545341/14708140126500199900781250:ℝ),(84806629174728474076250842257414713/367703503162504997519531250:ℝ),(9048879441076253815886459614269289/122567834387501665839843750:ℝ)],
![(29770822873577640827144908070359439/735407006325009995039062500:ℝ),(85757083677348319394481991705015909/735407006325009995039062500:ℝ),(82260074804830796764429506881336351/735407006325009995039062500:ℝ),(8757866160810785880879267488476627/245135668775003331679687500:ℝ)]]
theorem row117_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (8757866160810785880879267488476627/3743465530566142904374394880000000000:ℝ) row117_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row117_coefficients,Fin.sum_univ_succ]
 ring
theorem row117_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row117_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row117_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row117_pos
