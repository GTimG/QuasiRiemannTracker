/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row032_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2144448059035296625339104002819595357178/970248603849384323245376953125:ℝ),(6368946165381806752679305467563712397306/970248603849384323245376953125:ℝ),(6304819095857380210732067603097694734848/970248603849384323245376953125:ℝ),(416064131317054695578697105795715538944/194049720769876864649075390625:ℝ)],
![(4130786626260526016290808729944238984648/970248603849384323245376953125:ℝ),(2452982978999900387875767931241183762728/194049720769876864649075390625:ℝ),(12138014642768479042155577175511519471616/970248603849384323245376953125:ℝ),(4003885691938036902924522561749839642624/970248603849384323245376953125:ℝ)],
![(397549833258415110613267780453850009096/194049720769876864649075390625:ℝ),(5900201775072500709598869228079792264744/970248603849384323245376953125:ℝ),(5837429748883717902149930597614021142528/970248603849384323245376953125:ℝ),(1924976790739371025153900334303478923264/970248603849384323245376953125:ℝ)]]
theorem row032_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (117491259200401063546990987201140071/904337244471086236561195008000000000:ℝ) row032_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row032_coefficients,Fin.sum_univ_succ]
 ring
theorem row032_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row032_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_coefficients]
#print axioms row032_identity
#print axioms row032_pos
end
end LewkoStage1Finite
