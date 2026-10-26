/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row114_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2041663251368551865363996/34312948998046875:ℝ),(1189522856798676444329708/6862589799609375:ℝ),(5772624183076737763831634/34312948998046875:ℝ),(124444876696793827169806/2287529933203125:ℝ)],
![(3937850506099887380175592/34312948998046875:ℝ),(11448968745031626623295128/34312948998046875:ℝ),(11089254110852893262108416/34312948998046875:ℝ),(238542391461410267932592/2287529933203125:ℝ)],
![(1915330299932215644634436/34312948998046875:ℝ),(5558567219242978557936364/34312948998046875:ℝ),(5373627198617046249018692/34312948998046875:ℝ),(576796759768761111905588/11437649666015625:ℝ)]]
theorem row114_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (144199189942190277976397/43666072229904384000000000:ℝ) row114_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row114_coefficients,Fin.sum_univ_succ]
 ring
theorem row114_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row114_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row114_coefficients]
#print axioms row114_identity
#print axioms row114_pos
end
end LewkoStage2Finite
