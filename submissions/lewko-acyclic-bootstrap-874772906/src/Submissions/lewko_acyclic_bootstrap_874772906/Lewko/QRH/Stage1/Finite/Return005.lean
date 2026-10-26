/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1545661048875463637309/2635122023437500:ℝ),(40338038191371180945763/23716098210937500:ℝ),(38956287946847175597917/23716098210937500:ℝ),(2505839839071033477587/4743219642187500:ℝ)],
![(16625670697174867905343/15810732140625000:ℝ),(5763896550004358479741/1897287856875000:ℝ),(34655077940470679847149/11858049105468750:ℝ),(443999101032983611111/474321964218750:ℝ)],
![(118477373978123329190677/252971714250000000:ℝ),(1022548847131403747964287/758915142750000000:ℝ),(30602805400638375268739/23716098210937500:ℝ),(9755407738231070256481/23716098210937500:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (9755407738231070256481/44210011373568000000000:ℝ) row005_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ]
 ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
#print axioms row005_identity
#print axioms row005_pos
end
end LewkoStage1Finite
