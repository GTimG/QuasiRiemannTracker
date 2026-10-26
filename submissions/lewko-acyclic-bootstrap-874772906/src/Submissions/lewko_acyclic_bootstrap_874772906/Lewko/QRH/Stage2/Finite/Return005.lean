/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(23184914587096473892489/39526829929687500:ℝ),(67230060276274863448223/39526829929687500:ℝ),(64927143266017837084961/39526829929687500:ℝ),(20881997576839447529227/39526829929687500:ℝ)],
![(83128349072368904747777/79053659859375000:ℝ),(240162343259901157229017/79053659859375000:ℝ),(57758460051112092997873/19763414964843750:ℝ),(18499961504229029877563/19763414964843750:ℝ)],
![(65820759550490202517523/140539839750000000:ℝ),(189360886529705889789779/140539839750000000:ℝ),(5667185846094931943239/4391869992187500:ℝ),(1806556877994441715981/4391869992187500:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1806556877994441715981/8187039055872000000000:ℝ) row005_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage2Finite
