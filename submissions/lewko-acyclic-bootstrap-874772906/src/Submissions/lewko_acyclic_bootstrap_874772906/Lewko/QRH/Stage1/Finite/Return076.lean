/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row076_coefficients : Fin 3 → Fin 4 → ℝ := ![![(966110706936506782724584633481/13116755042957692283203125:ℝ),(2626258182772557561400464564409/13116755042957692283203125:ℝ),(947571739348298899401884381531/5246702017183076913281250:ℝ),(472425608567955313938611306933/8744503361971794855468750:ℝ)],
![(1751576472147054036738506275606/13116755042957692283203125:ℝ),(4661947034800414890128036020634/13116755042957692283203125:ℝ),(164059851313470604330078036012/524670201718307691328125:ℝ),(396935640296124752420129968424/4372251680985897427734375:ℝ)],
![(177425961776016364484273774227/2623351008591538456640625:ℝ),(466962188077362415626869028881/2623351008591538456640625:ℝ),(405190531091919002125045671331/2623351008591538456640625:ℝ),(38539627548893576342223055559/874450336197179485546875:ℝ)]]
theorem row076_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (38539627548893576342223055559/13040748597024621173145600000000:ℝ) row076_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row076_coefficients,Fin.sum_univ_succ]
 ring
theorem row076_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row076_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_coefficients]
#print axioms row076_identity
#print axioms row076_pos
end
end LewkoStage1Finite
