/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row191_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4452154483806632576531601834902753/413914024984270709837049187500000:ℝ),(472144243951367290767334757420129/21784948683382668938792062500000:ℝ),(5594457296194470966165095248033873/413914024984270709837049187500000:ℝ),(40802539195663430666002757678167/16556560999370828393481967500000:ℝ)],
![(7953581768732251697495661413415377/206957012492135354918524593750000:ℝ),(15509723238030757106965127126483399/206957012492135354918524593750000:ℝ),(9092211037855384989824698195386427/206957012492135354918524593750000:ℝ),(284890847697960215484139396463681/41391402498427070983704918750000:ℝ)],
![(24700257853154533533245294991928001/413914024984270709837049187500000:ℝ),(56395084013939391450241275173983667/413914024984270709837049187500000:ℝ),(42385676030528039187867658219737451/413914024984270709837049187500000:ℝ),(2093523841921804853000521407536357/82782804996854141967409837500000:ℝ)]]
theorem row191_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (40802539195663430666002757678167/7535074872602545899966904320000000:ℝ) row191_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row191_coefficients,Fin.sum_univ_succ]
 ring
theorem row191_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row191_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row191_coefficients]
#print axioms row191_identity
#print axioms row191_pos
end
end LewkoStage1Finite
