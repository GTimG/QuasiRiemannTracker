/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row138_coefficients : Fin 3 → Fin 4 → ℝ := ![![(308323658942474869048754671427/1380711057153441292968750:ℝ),(3002564795490422305797669563197/5246702017183076913281250:ℝ),(6300488549312914332553054791968/13116755042957692283203125:ℝ),(1722370262267546329897073700032/13116755042957692283203125:ℝ)],
![(5980765141457813295500688057134/13116755042957692283203125:ℝ),(15260928208604852102681455169726/13116755042957692283203125:ℝ),(134058951929385574611381087488/138071105715344129296875:ℝ),(3453800863096770126543342448768/13116755042957692283203125:ℝ)],
![(629523257340252879663678313418/2623351008591538456640625:ℝ),(8036685930066993339994530182626/13116755042957692283203125:ℝ),(6711801950726909706793443228992/13116755042957692283203125:ℝ),(1821875091478988993787398363456/13116755042957692283203125:ℝ)]]
theorem row138_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (26912035347930411404641776563/12225701809710582349824000000000:ℝ) row138_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row138_coefficients,Fin.sum_univ_succ]
 ring
theorem row138_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row138_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row138_coefficients]
#print axioms row138_identity
#print axioms row138_pos
end
end LewkoStage1Finite
