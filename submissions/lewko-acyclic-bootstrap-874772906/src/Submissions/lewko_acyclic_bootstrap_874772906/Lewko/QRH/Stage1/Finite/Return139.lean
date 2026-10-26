/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row139_coefficients : Fin 3 → Fin 4 → ℝ := ![![(191090123696302121434305732043/17489006723943589710937500:ℝ),(1326987993497517189791381988721/52467020171830769132812500:ℝ),(2568658349736739617233290912/138071105715344129296875:ℝ),(55378833652289614432569875992/13116755042957692283203125:ℝ)],
![(4198487862179673670217991182/174890067239435897109375:ℝ),(730219540064471256789569183738/13116755042957692283203125:ℝ),(538430022496277781519137989456/13116755042957692283203125:ℝ),(122629499795904720179605644368/13116755042957692283203125:ℝ)],
![(61425667449980251747183647748/4372251680985897427734375:ℝ),(435129047403755183540624397724/13116755042957692283203125:ℝ),(329663311964674181770375424696/13116755042957692283203125:ℝ),(78556227474835755389676970216/13116755042957692283203125:ℝ)]]
theorem row139_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6922354206536201804071234499/3056425452427645587456000000000:ℝ) row139_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row139_coefficients,Fin.sum_univ_succ]
 ring
theorem row139_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row139_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row139_coefficients]
#print axioms row139_identity
#print axioms row139_pos
end
end LewkoStage1Finite
