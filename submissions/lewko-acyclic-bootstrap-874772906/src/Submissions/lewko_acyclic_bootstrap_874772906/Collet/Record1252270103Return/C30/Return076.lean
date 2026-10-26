/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row076_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9839139114668610760211143786/131168756457220798828125:ℝ), (26782908245908103757198714314/131168756457220798828125:ℝ), (4839195424479530752060779299/26233751291444159765625:ℝ), (2416924465812169135488254489/43722918819073599609375:ℝ)],
![(17811208284987337257312904796/131168756457220798828125:ℝ), (47480265444621966273962067844/131168756457220798828125:ℝ), (1674018749667635819157153512/5246750258288831953125:ℝ), (4059407865336049297166141584/43722918819073599609375:ℝ)],
![(1798044396563587072660377182/26233751291444159765625:ℝ), (4738637652836946027925038346/26233751291444159765625:ℝ), (4118605933780858913451457646/26233751291444159765625:ℝ), (392552818945162261218515494/8744583763814719921875:ℝ)]]
theorem row076_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (196276409472581130609257747/65204342504716684492800000000:ℝ) row076_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row076_coefficients,Fin.sum_univ_succ]
 ring
theorem row076_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row076_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_coefficients]
#print axioms row076_identity
#print axioms row076_pos
end
end Record1252270103Return.C30
