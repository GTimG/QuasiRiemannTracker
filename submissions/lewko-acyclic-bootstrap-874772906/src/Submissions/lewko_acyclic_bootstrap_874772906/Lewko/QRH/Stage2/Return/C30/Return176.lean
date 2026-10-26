/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row176_coefficients : Fin 3 → Fin 4 → ℝ := ![![(100750899452850595291925748925069117/15789079912081912641421875000000:ℝ), (197018301243973012942072918427692733/15789079912081912641421875000000:ℝ), (867942458325277182828337000139627/131575665934015938678515625000:ℝ), (119183713069255098922559181617291/246704373626279885022216796875:ℝ)],
![(2135411038884905353401451176108191/131575665934015938678515625000:ℝ), (22300585731268880566123446245999419/657878329670079693392578125000:ℝ), (5132192210976947098823941804434443/246704373626279885022216796875:ℝ), (764575001541728584670956227934394/246704373626279885022216796875:ℝ)],
![(10646010208971014600180981356278233/986817494505119540088867187500:ℝ), (23806087988928299722367676979325953/986817494505119540088867187500:ℝ), (4145010729212684502405912189267833/246704373626279885022216796875:ℝ), (31488702281971314490050962901839/9137199023195551297119140625:ℝ)]]
theorem row176_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (119183713069255098922559181617291/459890284941422323052544000000000000:ℝ) row176_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row176_coefficients,Fin.sum_univ_succ]
 ring
theorem row176_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row176_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row176_coefficients]
#print axioms row176_identity
#print axioms row176_pos
end
end LewkoStage2Return.C30
