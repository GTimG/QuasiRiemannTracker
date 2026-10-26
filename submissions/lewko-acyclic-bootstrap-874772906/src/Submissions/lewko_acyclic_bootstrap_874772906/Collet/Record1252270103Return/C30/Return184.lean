/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row184_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3115978793916425229626818229/4602956194975271484375:ℝ), (8071146643457199113761681343/4602956194975271484375:ℝ), (6832613274469679822357799799/4602956194975271484375:ℝ), (375489084985781187644587337/920591238995054296875:ℝ)],
![(5728044809711630662001870026/4602956194975271484375:ℝ), (14461613496218214203284774462/4602956194975271484375:ℝ), (11818807578581128712732356646/4602956194975271484375:ℝ), (617047778414909034289890442/920591238995054296875:ℝ)],
![(2931249091835058578279610797/4602956194975271484375:ℝ), (7340339765636017243150303919/4602956194975271484375:ℝ), (5928450730787461790043636397/4602956194975271484375:ℝ), (60774402279460125006917731/184118247799010859375:ℝ)]]
theorem row184_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (60774402279460125006917731/87864650321508402462720000000:ℝ) row184_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row184_coefficients,Fin.sum_univ_succ]
 ring
theorem row184_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row184_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row184_coefficients]
#print axioms row184_identity
#print axioms row184_pos
end
end Record1252270103Return.C30
