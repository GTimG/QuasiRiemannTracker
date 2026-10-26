/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row044_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1153512929332571013176227784843/741128069091796875000:ℝ),(2415451382123650845077603707/520089873046875000:ℝ),(6847076068646945816789321856869/1482256138183593750000:ℝ),(151337699217312195644707124107/98817075878906250000:ℝ)],
![(1118605602553498578635571742537/370564034545898437500:ℝ),(667459417365209893990581206587/74112806909179687500:ℝ),(829704637746041584184791284232/92641008636474609375:ℝ),(36670902223720514847394361551/12352134484863281250:ℝ)],
![(19025344474842933511068674389/13002246826171875000:ℝ),(6810137670889594341544792573/1560269619140625000:ℝ),(169280993826387825811562322943/39006740478515625000:ℝ),(3740239031911784520409902119/2600449365234375000:ℝ)]]
theorem row044_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (3740239031911784520409902119/39711448812748800000000000000:ℝ) row044_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row044_coefficients,Fin.sum_univ_succ]
 ring
theorem row044_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row044_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_coefficients]
#print axioms row044_identity
#print axioms row044_pos
end
end LewkoStage1Finite
