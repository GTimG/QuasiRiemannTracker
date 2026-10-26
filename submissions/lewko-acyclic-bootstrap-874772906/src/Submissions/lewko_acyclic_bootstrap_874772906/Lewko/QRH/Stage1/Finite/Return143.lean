/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row143_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2317750632606726360747549381919518709/18628773193908179006311237500000000:ℝ),(25756724452669506385655554480099478539/93143865969540895031556187500000000:ℝ),(18261462369157746877099441800372585143/93143865969540895031556187500000000:ℝ),(1347736807216340793791995452040233383/31047955323180298343852062500000000:ℝ)],
![(2645411930184758776845076831390060381/9314386596954089503155618750000000:ℝ),(5308464815214255314789041902900587183/9314386596954089503155618750000000:ℝ),(3119825707017163448311772318819315533/9314386596954089503155618750000000:ℝ),(147229541541937312075370961727929577/3104795532318029834385206250000000:ℝ)],
![(6080505756527863914973266091629028993/18628773193908179006311237500000000:ℝ),(70441495055763652447723158260571066091/93143865969540895031556187500000000:ℝ),(26427633813342058498313784862178556181/46571932984770447515778093750000000:ℝ),(1058597489445489318142336183832807603/7761988830795074585963015625000000:ℝ)]]
theorem row143_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (147229541541937312075370961727929577/90433724447108623656119500800000000000:ℝ) row143_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row143_coefficients,Fin.sum_univ_succ]
 ring
theorem row143_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row143_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row143_coefficients]
#print axioms row143_identity
#print axioms row143_pos
end
end LewkoStage1Finite
