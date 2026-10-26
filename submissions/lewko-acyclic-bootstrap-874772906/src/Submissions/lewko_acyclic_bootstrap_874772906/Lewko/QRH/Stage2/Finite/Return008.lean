/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8895149857721245462862443/19763414964843750:ℝ),(351982452010712342101153/263512199531250:ℝ),(4352122050407830796332592/3293902494140625:ℝ),(860919825936480458327152/1976341496484375:ℝ)],
![(11476444518914041418670341/13175609976562500:ℝ),(4085791087670850555688039/1581073197187500:ℝ),(25251217619030370524801056/9881707482421875:ℝ),(924706301141453957305952/1097967498046875:ℝ)],
![(26636687969006899318981543/63242927887500000:ℝ),(394993846236631751966348867/316214639437500000:ℝ),(12201590163853399365962224/9881707482421875:ℝ),(4020014964115985135604688/9881707482421875:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (251250935257249070975293/1178933624045568000000000:ℝ) row008_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage2Finite
