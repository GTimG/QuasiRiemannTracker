/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row195_coefficients : Fin 3 → Fin 4 → ℝ := ![![(718549027117371166210409233174955293/25869626561516919364815574218750:ℝ),(342926261199136340009334405693123919/5173925312303383872963114843750:ℝ),(650931701458156756491423977524551413/12934813280758459682407787109375:ℝ),(50916432955628447781005352795677254/4311604426919486560802595703125:ℝ)],
![(136205694228594784449471807423839573/2586962656151691936481557421875:ℝ),(1550401905891672038221470315306176003/12934813280758459682407787109375:ℝ),(1088763446758978421691281567377791961/12934813280758459682407787109375:ℝ),(73025364631488882475888969365687941/4311604426919486560802595703125:ℝ)],
![(838172969321408136158708723804385697/25869626561516919364815574218750:ℝ),(1958301081904345888151611228147063091/25869626561516919364815574218750:ℝ),(1436198335907599948150578863867056591/25869626561516919364815574218750:ℝ),(105240475139400858612001978695626399/8623208853838973121605191406250:ℝ)]]
theorem row195_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (73025364631488882475888969365687941/128598611159083450026101833728000000000:ℝ) row195_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
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
end LewkoStage1Finite
