/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row097_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1791568664970947128339586861521/26233510085915384566406250:ℝ),(4721549022405974606759237646563/26233510085915384566406250:ℝ),(4103832452551540471741004071063/26233510085915384566406250:ℝ),(391165957892530257921180262007/8744503361971794855468750:ℝ)],
![(362850362116811347288763665637/2623351008591538456640625:ℝ),(4729223868379183872899891914739/13116755042957692283203125:ℝ),(4054241480633965384739509884073/13116755042957692283203125:ℝ),(379626593085341268923280849173/4372251680985897427734375:ℝ)],
![(2040263043536235481362944252869/26233510085915384566406250:ℝ),(213405715642812105514163742371/1049340403436615382656250:ℝ),(2295710975351772299746996258724/13116755042957692283203125:ℝ),(216018915871396926222981681007/4372251680985897427734375:ℝ)]]
theorem row097_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (379626593085341268923280849173/130407485970246211731456000000000:ℝ) row097_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row097_coefficients,Fin.sum_univ_succ]
 ring
theorem row097_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row097_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row097_coefficients]
#print axioms row097_identity
#print axioms row097_pos
end
end LewkoStage1Finite
