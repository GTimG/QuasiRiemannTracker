/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row074_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20161484381112037903083428941/5246702017183076913281250:ℝ),(14082625093668866884132167281/1380711057153441292968750:ℝ),(235896853261576873615518975403/26233510085915384566406250:ℝ),(69077722957201037203174941769/26233510085915384566406250:ℝ)],
![(82078596939555697536793519481/13116755042957692283203125:ℝ),(41088411371291794742120277799/2623351008591538456640625:ℝ),(168513712845324465693197970697/13116755042957692283203125:ℝ),(45079408640636745607827601183/13116755042957692283203125:ℝ)],
![(91838021714419905050176546787/26233510085915384566406250:ℝ),(225565987619280716030627741111/26233510085915384566406250:ℝ),(360627253012094923968492774347/52467020171830769132812500:ℝ),(92994210482912192228684135699/52467020171830769132812500:ℝ)]]
theorem row074_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (45079408640636745607827601183/12225701809710582349824000000000:ℝ) row074_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row074_coefficients,Fin.sum_univ_succ]
 ring
theorem row074_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row074_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row074_coefficients]
#print axioms row074_identity
#print axioms row074_pos
end
end LewkoStage1Finite
