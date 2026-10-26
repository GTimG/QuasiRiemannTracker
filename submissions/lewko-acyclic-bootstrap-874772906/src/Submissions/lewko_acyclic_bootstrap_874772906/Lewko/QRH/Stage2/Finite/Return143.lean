/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row143_coefficients : Fin 3 → Fin 4 → ℝ := ![![(236504311068981182877722607363768779/1900890927207190049608237500000000:ℝ),(2628226882904369917173644333563720949/9504454636035950248041187500000000:ℝ),(1863406376578448087068685412157271113/9504454636035950248041187500000000:ℝ),(137523460506692083502386015554131353/3168151545345316749347062500000000:ℝ)],
![(269939106631742902161912183987904931/950445463603595024804118750000000:ℝ),(541678124783566421993040607052195953/950445463603595024804118750000000:ℝ),(318348197029591190026268861931883283/950445463603595024804118750000000:ℝ),(15023326209365106687397206080864087/316815154534531674934706250000000:ℝ)],
![(620458134040111085996119586455081823/1900890927207190049608237500000000:ℝ),(7187888377881519169950450117157610981/9504454636035950248041187500000000:ℝ),(2696689941358359673550844379756387571/4752227318017975124020593750000000:ℝ),(108019847763601081761226701661922773/792037886336329187336765625000000:ℝ)]]
theorem row143_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (15023326209365106687397206080864087/9227910207811141266009292800000000000:ℝ) row143_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
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
end LewkoStage2Finite
