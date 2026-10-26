/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row196_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69299528199220425983362131559/115045786711731287109375:ℝ),(176244002954143385327038498693/115045786711731287109375:ℝ),(145545455544371408602279524929/115045786711731287109375:ℝ),(7720196157889689851720631559/23009157342346257421875:ℝ)],
![(127420780038410785661676425726/115045786711731287109375:ℝ),(314719055706887950403551373162/115045786711731287109375:ℝ),(249167875424084640850751136766/115045786711731287109375:ℝ),(12373919951121495221775237866/23009157342346257421875:ℝ)],
![(66082005795623396855068195267/115045786711731287109375:ℝ),(162164901450501078096413401789/115045786711731287109375:ℝ),(127121351108430667925540308532/115045786711731287109375:ℝ),(6207691090710597336839020402/23009157342346257421875:ℝ)]]
theorem row196_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (6186959975560747610887618933/10980397588210605726105600000000:ℝ) row196_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
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
end LewkoStage1Finite
