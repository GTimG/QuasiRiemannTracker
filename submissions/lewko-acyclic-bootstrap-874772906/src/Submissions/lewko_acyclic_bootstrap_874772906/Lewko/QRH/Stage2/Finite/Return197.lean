/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row197_coefficients : Fin 3 → Fin 4 → ℝ := ![![(756519430861827753833116496/399464436079880859375:ℝ),(16708918719744639161743976912/3595179924718927734375:ℝ),(13110968407558026761311788544/3595179924718927734375:ℝ),(3210724565569837384065860096/3595179924718927734375:ℝ)],
![(468846174410864810126372824/133154812026626953125:ℝ),(30287699663945842636642609096/3595179924718927734375:ℝ),(22842172876268907357552705536/3595179924718927734375:ℝ),(5213319921416414594322162688/3595179924718927734375:ℝ)],
![(676966320648489689973372061/399464436079880859375:ℝ),(14300436124442818791929861381/3595179924718927734375:ℝ),(10446986682227982338903210368/3595179924718927734375:ℝ),(2239247443621570756733697536/3595179924718927734375:ℝ)]]
theorem row197_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (4373530163323380384245503/13403802256860708864000000000:ℝ) row197_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row197_coefficients,Fin.sum_univ_succ]
 ring
theorem row197_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row197_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row197_coefficients]
#print axioms row197_identity
#print axioms row197_pos
end
end LewkoStage2Finite
