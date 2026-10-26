/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row198_coefficients : Fin 3 → Fin 4 → ℝ := ![![(54985796450832024808955436360487/4793607781307088134765625:ℝ), (354910387681880686532641390187/11836068595819970703125:ℝ), (245704336261877731354931470422793/9587215562614176269531250:ℝ), (22732838380406141627134272364099/3195738520871392089843750:ℝ)],
![(104929312282280874995254643512954/4793607781307088134765625:ℝ), (270929394269802732682332942128102/4793607781307088134765625:ℝ), (227748727240140752683917938752192/4793607781307088134765625:ℝ), (20582881750872964998946546712348/1597869260435696044921875:ℝ)],
![(17511157415217645469359553351739/1597869260435696044921875:ℝ), (134928985861832644534897702677467/4793607781307088134765625:ℝ), (112603411715536441413299146605233/4793607781307088134765625:ℝ), (1118811040716916047647411258629/177541028937299560546875:ℝ)]]
theorem row198_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (3356433122150748142942233775887/8133684405161506635776000000000000:ℝ) row198_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row198_coefficients,Fin.sum_univ_succ]
 ring
theorem row198_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row198_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row198_coefficients]
#print axioms row198_identity
#print axioms row198_pos
end
end Record1252270103Finite
