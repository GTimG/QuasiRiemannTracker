/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row147_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19213415831804195466661354372638034163/41422358039673009375000000000000:ℝ),(46381351653176946782397235419055685993/41422358039673009375000000000000:ℝ),(35466988400046035114107709158140673621/41422358039673009375000000000000:ℝ),(8299052578673283798371828111723021791/41422358039673009375000000000000:ℝ)],
![(17523751153822419715280058304565681003/20711179019836504687500000000000:ℝ),(40548109257362696742554611311562747481/20711179019836504687500000000000:ℝ),(5776783897226992090386150418048725167/4142235803967300937500000000000:ℝ),(5859561382594683424656199083246559357/20711179019836504687500000000000:ℝ)],
![(18694449826663561637214744195870138623/41422358039673009375000000000000:ℝ),(8645299392438915663933596949973677133/8284471607934601875000000000000:ℝ),(7685889943986147462296607050084065753/10355589509918252343750000000000:ℝ),(621151264041357316673318764633801597/4142235803967300937500000000000:ℝ)]]
theorem row147_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (5859561382594683424656199083246559357/19767519233733138422169600000000000000000:ℝ) row147_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row147_coefficients,Fin.sum_univ_succ]
 ring
theorem row147_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row147_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row147_coefficients]
#print axioms row147_identity
#print axioms row147_pos
end
end LewkoStage1Finite
