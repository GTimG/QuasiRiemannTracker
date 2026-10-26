/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row097_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9090631739731255377037625893/131168756457220798828125:ℝ), (23994417534924690180832411679/131168756457220798828125:ℝ), (20894258939644254608464508179/131168756457220798828125:ℝ), (1996234013696917977337824131/43722918819073599609375:ℝ)],
![(3670099832022208844673223762/26233751291444159765625:ℝ), (47894946153596874366953138974/131168756457220798828125:ℝ), (41124108475406202872514755018/131168756457220798828125:ℝ), (3858588351509409269694661618/43722918819073599609375:ℝ)],
![(10278020232878997712528617817/131168756457220798828125:ℝ), (5379271936828610361796513099/26233751291444159765625:ℝ), (23168387585373001112682593764/131168756457220798828125:ℝ), (2182635033014422436771527862/43722918819073599609375:ℝ)]]
theorem row097_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1929294175754704634847330809/652043425047166844928000000000:ℝ) row097_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row097_coefficients,Fin.sum_univ_succ]
 ring
theorem row097_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row097_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row097_coefficients]
#print axioms row097_identity
#print axioms row097_pos
end
end Record1252270103Return.C30
