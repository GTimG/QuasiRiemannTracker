/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(463564064076729166763/790542914062500:ℝ), (1344210717413996063309/790542914062500:ℝ), (144240504927070583579/87838101562500:ℝ), (27834526067091223711/52702860937500:ℝ)],
![(1662050936733037746067/1581085828125000:ℝ), (320116566743100703669/105405721875000:ℝ), (1154807022510531169507/395271457031250:ℝ), (73976526281432593453/79054291406250:ℝ)],
![(3947925062646699921211/8432457750000000:ℝ), (34073480963387870984561/25297373250000000:ℝ), (1019747400166162651277/790542914062500:ℝ), (325069094683419800623/790542914062500:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (325069094683419800623/1473678802944000000000:ℝ) row005_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage1Return.C30
