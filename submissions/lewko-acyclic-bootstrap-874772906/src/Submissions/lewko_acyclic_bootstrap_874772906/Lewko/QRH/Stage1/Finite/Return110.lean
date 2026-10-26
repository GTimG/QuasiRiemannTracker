/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row110_coefficients : Fin 3 → Fin 4 → ℝ := ![![(561203116241437141064/38888008927734375:ℝ),(4530969807898740109672/116664026783203125:ℝ),(4061955328011573091928/116664026783203125:ℝ),(1214594868837144405448/116664026783203125:ℝ)],
![(192654644139682890548/7777601785546875:ℝ),(7513804182281908059404/116664026783203125:ℝ),(6469236133957671691408/116664026783203125:ℝ),(1845251613771006990224/116664026783203125:ℝ)],
![(1789369487275618719599/155552035710937500:ℝ),(13512871671713539367533/466656107132812500:ℝ),(558195591583516038208/23332805356640625:ℝ),(754787155445909388856/116664026783203125:ℝ)]]
theorem row110_identity (δ p : ℝ) : rowMargin .newSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (94348394430738673607/27184688566272000000000:ℝ) row110_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row110_coefficients,Fin.sum_univ_succ]
 ring
theorem row110_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capC δ p := by
 rw [row110_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row110_coefficients]
#print axioms row110_identity
#print axioms row110_pos
end
end LewkoStage1Finite
