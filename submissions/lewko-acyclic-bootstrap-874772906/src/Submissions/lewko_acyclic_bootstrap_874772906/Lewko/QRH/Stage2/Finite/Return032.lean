/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row032_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1191356347400991651083917241573765032958/539025783756668474715298828125:ℝ),(3538292438063140152094171803597137433598/539025783756668474715298828125:ℝ),(1501142724535246066277846797652528508416/231011050181429346306556640625:ℝ),(3467190244884235404710766656872582356992/1617077351270005424145896484375:ℝ)],
![(2294874350309196485352303096040697480344/539025783756668474715298828125:ℝ),(973402917084662372910636436996677173416/77003683393809782102185546875:ℝ),(4045992249993530281599344641468643190784/323415470254001084829179296875:ℝ),(6673121905298123942172087606035087753216/1617077351270005424145896484375:ℝ)],
![(1104301666858808730258933971828781780152/539025783756668474715298828125:ℝ),(2697843347193151277721126335851080008/443642620375858826926171875:ℝ),(3243006387210806664319338979257528522752/539025783756668474715298828125:ℝ),(1069428193138852454700585965527248093184/539025783756668474715298828125:ℝ)]]
theorem row032_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (65272716866385037518346311372512701/502408444647495468927172608000000000:ℝ) row032_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row032_coefficients,Fin.sum_univ_succ]
 ring
theorem row032_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row032_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_coefficients]
#print axioms row032_identity
#print axioms row032_pos
end
end LewkoStage2Finite
