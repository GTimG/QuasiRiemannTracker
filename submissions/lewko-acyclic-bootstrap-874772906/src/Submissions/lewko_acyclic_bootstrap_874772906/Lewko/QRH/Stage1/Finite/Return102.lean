/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row102_coefficients : Fin 3 → Fin 4 → ℝ := ![![(713917015234725496837723367622753496534/19091354420795422256845505859375:ℝ),(2043623360249971500322559666268029416918/19091354420795422256845505859375:ℝ),(1947136962352065711443970290888217004544/19091354420795422256845505859375:ℝ),(123484932574886285089673432823588216832/3818270884159084451369101171875:ℝ)],
![(1413628182833095489706894069425202253944/19091354420795422256845505859375:ℝ),(808053681178563585655668668390308188184/3818270884159084451369101171875:ℝ),(3843008795070128991965527313023224014848/19091354420795422256845505859375:ℝ),(1216356372624050072152506977996885327872/19091354420795422256845505859375:ℝ)],
![(141489660939658321281887550178717727288/3818270884159084451369101171875:ℝ),(2019727699045763559603876507648389694232/19091354420795422256845505859375:ℝ),(1918826555669678289203373834003676227584/19091354420795422256845505859375:ℝ),(606540912856023748055935264748875169792/19091354420795422256845505859375:ℝ)]]
theorem row102_identity (δ p : ℝ) : rowMargin .oldSwitch .P δ p =
 Record12518109.Bernstein.bsum 2 3 (37020319388185043216304642623832713/17794432047235538389683585024000000000:ℝ) row102_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row102_coefficients,Fin.sum_univ_succ]
 ring
theorem row102_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .P δ p := by
 rw [row102_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row102_coefficients]
#print axioms row102_identity
#print axioms row102_pos
end
end LewkoStage1Finite
