/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row095_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22945491357773237759419930196244154796/37318998047758674969568359375:ℝ), (65931266796897831721522897770990015404/37318998047758674969568359375:ℝ), (12614928683612395026684801980287960064/7463799609551734993913671875:ℝ), (20088688877881197870014551701693939712/37318998047758674969568359375:ℝ)],
![(45613450694164367547363970456975380736/37318998047758674969568359375:ℝ), (130998886243074752128611303359943610624/37318998047758674969568359375:ℝ), (25051030537403195439479042394453803008/7463799609551734993913671875:ℝ), (39869356683149752009744879069300785152/37318998047758674969568359375:ℝ)],
![(4536597188138268305055049430911971328/7463799609551734993913671875:ℝ), (13022489469882502418577254854157430784/7463799609551734993913671875:ℝ), (12445017378201870058579499275815747584/7463799609551734993913671875:ℝ), (3959088824260821795985293852570288128/7463799609551734993913671875:ℝ)]]
theorem row095_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (471960166008570408342515689441/217398920538481113138278400000000:ℝ) row095_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row095_coefficients,Fin.sum_univ_succ]
 ring
theorem row095_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row095_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row095_coefficients]
#print axioms row095_identity
#print axioms row095_pos
end
end LewkoStage2Return.C30
