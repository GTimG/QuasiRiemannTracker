/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row077_coefficients : Fin 3 → Fin 4 → ℝ := ![![(153655484122103347231097/68625897996093750:ℝ),(438852021292149976050827/68625897996093750:ℝ),(83461960970180353154951/13725179599218750:ℝ),(5284530707234205478201/2745035919843750:ℝ)],
![(143369143620606513724649/34312948998046875:ℝ),(31290023437826200309079/2639457615234375:ℝ),(384029298312053189111023/34312948998046875:ℝ),(24125627448183819763529/6862589799609375:ℝ)],
![(137977643152345656894161/68625897996093750:ℝ),(389263139423960390161979/68625897996093750:ℝ),(365214264372817826403793/68625897996093750:ℝ),(4557150724048123725439/2745035919843750:ℝ)]]
theorem row077_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (4557150724048123725439/1309982166897131520000000:ℝ) row077_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row077_coefficients,Fin.sum_univ_succ]
 ring
theorem row077_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row077_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_coefficients]
#print axioms row077_identity
#print axioms row077_pos
end
end LewkoStage2Finite
