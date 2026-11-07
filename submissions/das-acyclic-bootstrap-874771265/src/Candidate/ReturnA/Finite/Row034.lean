/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row034_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1531021571458136311902579943321/4444036675863455039062500:ℝ),(12955109958298408833346840466491/13332110027590365117187500:ℝ),(3039123652351237591141550407592/3333027506897591279296875:ℝ),(189710485703391504895800362192/666605501379518255859375:ℝ)],
![(670124007136455299022893340506/1111009168965863759765625:ℝ),(5633997434532638454857935142318/3333027506897591279296875:ℝ),(5249917719230932802629149663232/3333027506897591279296875:ℝ),(1626161587155049134470207042432/3333027506897591279296875:ℝ)],
![(290659578550913464935590406532/1111009168965863759765625:ℝ),(2425123569863408730987605541964/3333027506897591279296875:ℝ),(448191539622225918195117534208/666605501379518255859375:ℝ),(687741562653582467320378348672/3333027506897591279296875:ℝ)]]
theorem row034_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5372980958231113025940455849/48540731264897898240000000000:ℝ) row034_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row034_coefficients,Fin.sum_univ_succ]
 ring
theorem row034_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row034_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row034_pos
