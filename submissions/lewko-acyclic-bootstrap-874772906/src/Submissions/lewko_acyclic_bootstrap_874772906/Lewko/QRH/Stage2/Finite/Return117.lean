/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row117_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1857090638040068071734948642493827023/43205822738904000132175359375:ℝ),(671382240666231685791555058783583972249/5400727842363000016521919921875:ℝ),(646764074521044257816065898640195209761/5400727842363000016521919921875:ℝ),(591215553305888380887575662872762437/15386689009581196628267578125:ℝ)],
![(89636958914053334235266932733466868174/1080145568472600003304383984375:ℝ),(1293468834611951275363024812226557894898/5400727842363000016521919921875:ℝ),(1243220360381367259433044612549188149594/5400727842363000016521919921875:ℝ),(14738267865253907089643198203332022058/200026957124555556167478515625:ℝ)],
![(43648469835131861030804544003005631071/1080145568472600003304383984375:ℝ),(628631238807517948505805826344515066153/5400727842363000016521919921875:ℝ),(602964163497222084027108182428472437723/5400727842363000016521919921875:ℝ),(95098118145759337895459190357523717/2667026094994074082233046875:ℝ)]]
theorem row117_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (285294354437278013686377571072571151/122184425126166799967916277104640000000:ℝ) row117_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row117_coefficients,Fin.sum_univ_succ]
 ring
theorem row117_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row117_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row117_coefficients]
#print axioms row117_identity
#print axioms row117_pos
end
end LewkoStage2Finite
