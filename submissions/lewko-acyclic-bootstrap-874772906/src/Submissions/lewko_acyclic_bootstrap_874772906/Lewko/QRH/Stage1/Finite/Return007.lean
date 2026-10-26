/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8949024811267810894266869/75891514275000000:ℝ),(132851081560841442049694587/379457571375000000:ℝ),(5258827942604307556585739/15178302855000000:ℝ),(43364741060605301336283233/379457571375000000:ℝ)],
![(41973016960464668818289209/189728785687500000:ℝ),(124543684138897534211275867/189728785687500000:ℝ),(24634474025817168242924371/37945757137500000:ℝ),(40601702950652975821635197/189728785687500000:ℝ)],
![(2067633711904047468202747/19971451125000000:ℝ),(6131049847360476256378249/19971451125000000:ℝ),(6059419712528114603623163/19971451125000000:ℝ),(1996003577071685815447661/19971451125000000:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (1996003577071685815447661/9530747715059712000000000:ℝ) row007_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ]
 ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
#print axioms row007_identity
#print axioms row007_pos
end
end LewkoStage1Finite
