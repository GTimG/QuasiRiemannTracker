/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row024_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1996205771436608425107105627380911747/1779737651856611760937500:ℝ),(446806852557958499848562046087366096929/133480323889245882070312500:ℝ),(777826378144484010040759899938339620864/233590566806180293623046875:ℝ),(257916388693423298321587743664349868032/233590566806180293623046875:ℝ)],
![(173849626686609617401214877701860856591/77863522268726764541015625:ℝ),(1556469242338080346369498454999236279789/233590566806180293623046875:ℝ),(1548308689728185785867697071729114947584/233590566806180293623046875:ℝ),(513388317467165551614273608382336237568/233590566806180293623046875:ℝ)],
![(86516521431814545510702230565916831141/77863522268726764541015625:ℝ),(774565326242985119238833259566694677807/233590566806180293623046875:ℝ),(154098077617991200679310706088133607424/46718113361236058724609375:ℝ),(255474621135284458626976574587348852736/233590566806180293623046875:ℝ)]]
theorem row024_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (31185866837803278640988351390057233/222947521130366118175703040000000000:ℝ) row024_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row024_coefficients,Fin.sum_univ_succ]
 ring
theorem row024_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row024_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row024_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row024_pos
