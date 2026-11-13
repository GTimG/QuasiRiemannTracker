/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row011_coefficients : Fin 3 → Fin 4 → ℝ := ![![(304659679177619208659684905756756/3333027506897591279296875:ℝ),(899774603804416002617647993975552/3333027506897591279296875:ℝ),(885662767173375882688860067001111/3333027506897591279296875:ℝ),(58109532759662868798570716068963/666605501379518255859375:ℝ)],
![(569812024039836238349959774247216/3333027506897591279296875:ℝ),(1681489312960682498207158416382832/3333027506897591279296875:ℝ),(1653730669636084116935938263321016/3333027506897591279296875:ℝ),(21682120176124062094682772347416/133321100275903651171875:ℝ)],
![(53158585057226245062772682825192/666605501379518255859375:ℝ),(156728120917491099909666450889976/666605501379518255859375:ℝ),(153999569864436969420002536254376/666605501379518255859375:ℝ),(50429994392368293024511893189592/666605501379518255859375:ℝ)]]
theorem row011_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6303749299046036628063986648699/39764567052204358238208000000000:ℝ) row011_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row011_coefficients,Fin.sum_univ_succ]
 ring
theorem row011_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row011_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row011_pos
