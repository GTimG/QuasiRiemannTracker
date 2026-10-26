/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1779030076278999050639701/3952683035156250:ℝ),(15839211277988549449073087/11858049105468750:ℝ),(7833820156913418958888016/5929024552734375:ℝ),(2582759632337642810311024/5929024552734375:ℝ)],
![(765096347315122395626089/878374007812500:ℝ),(61286870024956126070855699/23716098210937500:ℝ),(3030146298745054081026848/1185804910546875:ℝ),(4993414331863315057896416/5929024552734375:ℝ)],
![(1065467584364543335917317/2529717142500000:ℝ),(236996322420655857557881463/189728785687500000:ℝ),(7320954554427762266134832/5929024552734375:ℝ),(2412009129636665161007248/5929024552734375:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (150750570602291572562953/707360181977088000000000:ℝ) row008_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ]
 ring
theorem row008_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
#print axioms row008_identity
#print axioms row008_pos
end
end LewkoStage1Finite
