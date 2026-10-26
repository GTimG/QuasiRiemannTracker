/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row077_coefficients : Fin 3 → Fin 4 → ℝ := ![![(522428102713859661986171/233328053566406250:ℝ),(1492095279245865590650577/233328053566406250:ℝ),(1418851779843525279386521/233328053566406250:ℝ),(89836920662303870144423/46665610713281250:ℝ)],
![(487454643394387211165387/116664026783203125:ℝ),(1383017737085125504310129/116664026783203125:ℝ),(1305698351006922716011837/116664026783203125:ℝ),(82027051463236884573419/23332805356640625:ℝ)],
![(469123637166944198624003/233328053566406250:ℝ),(1323493660284083603188961/233328053566406250:ℝ),(1241727519729243011207683/233328053566406250:ℝ),(15494299864484144265709/9333122142656250:ℝ)]]
theorem row077_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (15494299864484144265709/4453939374698004480000000:ℝ) row077_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row077_coefficients,Fin.sum_univ_succ]
 ring
theorem row077_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row077_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_coefficients]
#print axioms row077_identity
#print axioms row077_pos
end
end LewkoStage1Finite
