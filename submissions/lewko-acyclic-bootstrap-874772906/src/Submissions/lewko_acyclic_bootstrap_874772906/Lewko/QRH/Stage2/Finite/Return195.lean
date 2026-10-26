/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row195_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22454045954032070152861384123169261/808425616787864268129428906250:ℝ),(267902221898853902611011086301325991/4042128083939321340647144531250:ℝ),(20340748196547630587713717338396733/404212808393932134064714453125:ℝ),(7955224184853167803201212384643774/673688013989886890107857421875:ℝ)],
![(4256318019447964074730578544226149/80842561678786426812942890625:ℝ),(242242295484157393989487447534818623/2021064041969660670323572265625:ℝ),(170111525650395616385831127826087981/2021064041969660670323572265625:ℝ),(11409376985011053565526517080224361/673688013989886890107857421875:ℝ)],
![(130962066850462605345811076349536437/4042128083939321340647144531250:ℝ),(305977401875527064707444096438913711/4042128083939321340647144531250:ℝ),(224399081687284940874903803092535611/4042128083939321340647144531250:ℝ),(16443082332812692516264856313552779/1347376027979773780215714843750:ℝ)]]
theorem row195_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (11409376985011053565526517080224361/20093527693012185192724955136000000000:ℝ) row195_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row195_coefficients,Fin.sum_univ_succ]
 ring
theorem row195_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row195_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row195_coefficients]
#print axioms row195_identity
#print axioms row195_pos
end
end LewkoStage2Finite
