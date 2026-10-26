/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row038_coefficients : Fin 3 → Fin 4 → ℝ := ![![(48384617178282333481630142011/17776302280717681406250000:ℝ),(80957893146435502852313033879/10665781368430608843750000:ℝ),(375454073751871763139472482091/53328906842153044218750000:ℝ),(38598824414656744075099246243/17776302280717681406250000:ℝ)],
![(106505611140789825464814928673/26664453421076522109375000:ℝ),(96639020177113329162304211873/8888151140358840703125000:ℝ),(262013371266385993062636234319/26664453421076522109375000:ℝ),(26189647469993101798096175791/8888151140358840703125000:ℝ)],
![(80083204154512855946309531113/53328906842153044218750000:ℝ),(11109546500763960860749126097/2806784570639633906250000:ℝ),(183993837436588522429525247497/53328906842153044218750000:ℝ),(17648729625933777850742127589/17776302280717681406250000:ℝ)]]
theorem row038_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (17648729625933777850742127589/258886165837580881920000000000:ℝ) row038_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row038_coefficients,Fin.sum_univ_succ]
 ring
theorem row038_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row038_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_coefficients]
#print axioms row038_identity
#print axioms row038_pos
end
end LewkoStage1Finite
