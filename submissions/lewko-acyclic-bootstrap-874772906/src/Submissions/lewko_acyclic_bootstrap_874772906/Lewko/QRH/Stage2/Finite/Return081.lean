/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row081_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32478371132447386308428018328692/19289345414141723501953125:ℝ),(91177704606505092137498028792608/19289345414141723501953125:ℝ),(85105233572011039780006358077471/19289345414141723501953125:ℝ),(5280991969658884377707224210211/3857869082828344700390625:ℝ)],
![(61885105804044067329036148870192/19289345414141723501953125:ℝ),(172568084711319275290302461071984/19289345414141723501953125:ℝ),(159867634256425834358807171946872/19289345414141723501953125:ℝ),(9836535175236899147971234449016/3857869082828344700390625:ℝ)],
![(6107054987660963457913853644264/3857869082828344700390625:ℝ),(16948602528762593412132841294072/3857869082828344700390625:ℝ),(15616484499479802721272222733352/3857869082828344700390625:ℝ),(4774728592802790592560110083544/3857869082828344700390625:ℝ)]]
theorem row081_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (596841074100348824070013760443/230130854763850773194342400000000:ℝ) row081_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row081_coefficients,Fin.sum_univ_succ]
 ring
theorem row081_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row081_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row081_coefficients]
#print axioms row081_identity
#print axioms row081_pos
end
end LewkoStage2Finite
