/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row216_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12341150882876014691970356749954381/404212808393932134064714453125:ℝ),(28332572781041968942912156988893583/404212808393932134064714453125:ℝ),(20174740762217756559658127654255773/404212808393932134064714453125:ℝ),(1392622965891187304089568669688857/134737602797977378021571484375:ℝ)],
![(147965625193023650397250180243426522/2021064041969660670323572265625:ℝ),(347060834201789360147078218793030918/2021064041969660670323572265625:ℝ),(51206992731813378017130790361801072/404212808393932134064714453125:ℝ),(18959935006713511991634025930216988/673688013989886890107857421875:ℝ)],
![(101468068602755953124192931370692263/2021064041969660670323572265625:ℝ),(250095486699612605102257577683864231/2021064041969660670323572265625:ℝ),(397906032047926228555105347899779969/4042128083939321340647144531250:ℝ),(33528417087012071933986612085937011/1347376027979773780215714843750:ℝ)]]
theorem row216_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1392622965891187304089568669688857/2009352769301218519272495513600000000:ℝ) row216_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row216_coefficients,Fin.sum_univ_succ]
 ring
theorem row216_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row216_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row216_coefficients]
#print axioms row216_identity
#print axioms row216_pos
end
end LewkoStage2Finite
