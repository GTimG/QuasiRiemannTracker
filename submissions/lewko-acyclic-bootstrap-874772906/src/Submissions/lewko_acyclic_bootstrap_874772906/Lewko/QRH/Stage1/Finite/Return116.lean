/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row116_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22085272046632349838636857219452/13116755042957692283203125:ℝ),(62000779956913150526002843203904/13116755042957692283203125:ℝ),(57871501425022656365703161559557/13116755042957692283203125:ℝ),(3591070829008920214407064802521/2623351008591538456640625:ℝ)],
![(42081840099368230464880576406672/13116755042957692283203125:ℝ),(117346205484581407499272426040144/13116755042957692283203125:ℝ),(108709902551568817323795746053672/13116755042957692283203125:ℝ),(1337767644995509434203368356808/524670201718307691328125:ℝ)],
![(4152795058862315899298140459064/2623351008591538456640625:ℝ),(11525043046156918657173810636392/2623351008591538456640625:ℝ),(10619203106395422404107481385592/2623351008591538456640625:ℝ),(3246813430525250758408686208264/2623351008591538456640625:ℝ)]]
theorem row116_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (405851678815656344801085776033/156488983164295454077747200000000:ℝ) row116_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row116_coefficients,Fin.sum_univ_succ]
 ring
theorem row116_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row116_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row116_coefficients]
#print axioms row116_identity
#print axioms row116_pos
end
end LewkoStage1Finite
