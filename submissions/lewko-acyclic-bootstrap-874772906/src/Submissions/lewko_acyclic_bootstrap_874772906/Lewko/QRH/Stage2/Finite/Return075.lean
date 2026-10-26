/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row075_coefficients : Fin 3 → Fin 4 → ℝ := ![![(165059922237329520344/11437649666015625:ℝ),(1332639724713552710968/34312948998046875:ℝ),(91899553687133100968/2639457615234375:ℝ),(357234239931166162648/34312948998046875:ℝ)],
![(21793533577625758588/879819205078125:ℝ),(2209944775408994863844/34312948998046875:ℝ),(1902718701865258572976/34312948998046875:ℝ),(542721735983668294064/34312948998046875:ℝ)],
![(526285556699134187093/45750598664062500:ℝ),(3974377394169448711711/137251795992187500:ℝ),(820876628782827290096/34312948998046875:ℝ),(221996447764815752488/34312948998046875:ℝ)]]
theorem row075_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (27749555970601969061/7995496624128000000000:ℝ) row075_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row075_coefficients,Fin.sum_univ_succ]
 ring
theorem row075_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row075_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_coefficients]
#print axioms row075_identity
#print axioms row075_pos
end
end LewkoStage2Finite
