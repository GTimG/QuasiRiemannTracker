/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row106_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3670640635129238102041335907/839472322749292306125000000:ℝ),(9801621739148912005474945081/839472322749292306125000000:ℝ),(8591321572910109704825882441/839472322749292306125000000:ℝ),(2460340468890435801392273267/839472322749292306125000000:ℝ)],
![(1010823243789749867349257719/419736161374646153062500000:ℝ),(2522775471527851956096782023/419736161374646153062500000:ℝ),(2121898034163469133705105789/419736161374646153062500000:ℝ),(121989161285073408991516297/83947232274929230612500000:ℝ)],
![(1708895143447430857157179531/839472322749292306125000000:ℝ),(530801333395745648771077157/167894464549858461225000000:ℝ),(1231208694349287139051246187/839472322749292306125000000:ℝ),(172746310362879493853039933/839472322749292306125000000:ℝ)]]
theorem row106_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (172746310362879493853039933/47756647694181962304000000000:ℝ) row106_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row106_coefficients,Fin.sum_univ_succ]
 ring
theorem row106_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row106_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row106_coefficients]
#print axioms row106_identity
#print axioms row106_pos
end
end LewkoStage1Finite
