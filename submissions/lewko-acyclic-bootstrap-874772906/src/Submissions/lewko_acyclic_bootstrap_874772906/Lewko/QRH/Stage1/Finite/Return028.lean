/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row028_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6101465179516481467128839489044208243/77619888307950745859630156250:ℝ),(17967573644270301113270827148450947289/77619888307950745859630156250:ℝ),(17633460302609602172279240310905401849/77619888307950745859630156250:ℝ),(5767345500188268322717752651498662803/77619888307950745859630156250:ℝ)],
![(142227340987784080453769854260966269531/970248603849384323245376953125:ℝ),(22022511424132276098257927429888670443/51065715992072859118177734375:ℝ),(21591679909193520167431522011601246339/51065715992072859118177734375:ℝ),(26808275168035093985661255262701042311/194049720769876864649075390625:ℝ)],
![(132269560993498778979906991817802908387/1940497207698768646490753906250:ℝ),(388721515190587430061983615353273929089/1940497207698768646490753906250:ℝ),(380703557873238179764923326693685820387/1940497207698768646490753906250:ℝ),(1307909778886196510011544572718050523/20426286396829143647271093750:ℝ)]]
theorem row028_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1307909778886196510011544572718050523/9747803561456761118301723033600000000:ℝ) row028_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row028_coefficients,Fin.sum_univ_succ]
 ring
theorem row028_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row028_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_coefficients]
#print axioms row028_identity
#print axioms row028_pos
end
end LewkoStage1Finite
