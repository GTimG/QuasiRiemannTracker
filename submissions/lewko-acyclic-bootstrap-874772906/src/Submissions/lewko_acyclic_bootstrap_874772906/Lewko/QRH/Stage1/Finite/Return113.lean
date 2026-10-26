/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row113_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35207047875288329407856/4320889880859375:ℝ),(2709197252094750627595984/116664026783203125:ℝ),(2570503528270727541243392/116664026783203125:ℝ),(162379313761752361531904/23332805356640625:ℝ)],
![(67521254326680671567192/4320889880859375:ℝ),(5176085114863128647681096/116664026783203125:ℝ),(978174199224640389656576/23332805356640625:ℝ),(1537859748080451432915968/116664026783203125:ℝ)],
![(10871732556443003322437/1440296626953125:ℝ),(2491084212925175500691797/116664026783203125:ℝ),(2344381401397752852291968/116664026783203125:ℝ),(733907525544460620717568/116664026783203125:ℝ)]]
theorem row113_identity (δ p : ℝ) : rowMargin .newSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1433413135829024649839/434955017060352000000000:ℝ) row113_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row113_coefficients,Fin.sum_univ_succ]
 ring
theorem row113_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capC δ p := by
 rw [row113_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row113_coefficients]
#print axioms row113_identity
#print axioms row113_pos
end
end LewkoStage1Finite
