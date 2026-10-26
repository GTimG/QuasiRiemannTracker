/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row034_coefficients : Fin 3 → Fin 4 → ℝ := ![![(306217574808682909570579756409/888815114035884070312500:ℝ),(2591136099695961154912472674459/2666445342107652210937500:ℝ),(607851950287624610266682981768/666611335526913052734375:ℝ),(1997043413868446977647446768/7016961426599084765625:ℝ)],
![(44677024959370556251617594238/74067926169657005859375:ℝ),(1126853335683109851685783567022/666611335526913052734375:ℝ),(1050034784420028896736157968928/666611335526913052734375:ℝ),(325248530492757962209495250048/666611335526913052734375:ℝ)],
![(3059730361627077732364672492/11694935710998474609375:ℝ),(485050060617097904273732718796/666611335526913052734375:ℝ),(89643116915519504220173252224/133322267105382610546875:ℝ),(137555894821336089878044874368/666611335526913052734375:ℝ)]]
theorem row034_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1074655428291688202172225581/9708231218909283072000000000:ℝ) row034_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row034_coefficients,Fin.sum_univ_succ]
 ring
theorem row034_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row034_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_coefficients]
#print axioms row034_identity
#print axioms row034_pos
end
end LewkoStage1Finite
