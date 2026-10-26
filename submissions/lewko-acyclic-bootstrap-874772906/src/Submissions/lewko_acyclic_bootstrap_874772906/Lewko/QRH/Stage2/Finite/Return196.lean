/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row196_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2165514245158977103494009233/3595179924718927734375:ℝ),(5507339799976788616885495523/3595179924718927734375:ℝ),(36384103431389195468947667/28761439397751421875:ℝ),(241237474821167584045394417/719035984943785546875:ℝ)],
![(3981717567303316970176492402/3595179924718927734375:ℝ),(9834430530160949851422060646/3595179924718927734375:ℝ),(7785961601202805436407497074/3595179924718927734375:ℝ),(386649727669034511032385766/719035984943785546875:ℝ)],
![(2064976728948109566675404309/3595179924718927734375:ℝ),(5067398037616975284229910891/3595179924718927734375:ℝ),(3972289807430068488960794092/3595179924718927734375:ℝ),(193973699752240554281257502/719035984943785546875:ℝ)]]
theorem row196_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (193324863834517255516192883/343137337775634146918400000000:ℝ) row196_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row196_coefficients,Fin.sum_univ_succ]
 ring
theorem row196_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row196_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row196_coefficients]
#print axioms row196_identity
#print axioms row196_pos
end
end LewkoStage2Finite
