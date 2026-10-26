/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row078_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31065073390319244751472/3812549888671875:ℝ),(796823540866886498470384/34312948998046875:ℝ),(756031247988507299383808/34312948998046875:ℝ),(238793367634494003676672/34312948998046875:ℝ)],
![(19859211089782171453768/1270849962890625:ℝ),(1522379442751678792619672/34312948998046875:ℝ),(1438492895440314752714752/34312948998046875:ℝ),(452312152112754589346816/34312948998046875:ℝ)],
![(28778140416597808912927/3812549888671875:ℝ),(732672476857517022038167/34312948998046875:ℝ),(689524570495985399240576/34312948998046875:ℝ),(215855357387848657418752/34312948998046875:ℝ)]]
theorem row078_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (421592494898141909021/127927945986048000000000:ℝ) row078_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row078_coefficients,Fin.sum_univ_succ]
 ring
theorem row078_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row078_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_coefficients]
#print axioms row078_identity
#print axioms row078_pos
end
end LewkoStage2Finite
