/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row064_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9764284740621203965362357485992583303543/9332078728609550318939736328125:ℝ),(9667956493217728370873701698353297095543/3110692909536516772979912109375:ℝ),(284318602233546210913773586186402649729/92396819095144062563759765625:ℝ),(55418666011258064639313652606779880933/54573559816430118824208984375:ℝ)],
![(18900986512363732239930715965983197537646/9332078728609550318939736328125:ℝ),(56129069042834208079033473696680570415562/9332078728609550318939736328125:ℝ),(55557795391297643523505168590254539646186/9332078728609550318939736328125:ℝ),(407326852302966680575498296879048150406/207379527302434451531994140625:ℝ)],
![(1015999339792989027379012004084096037767/1036897636512172257659970703125:ℝ),(27147035780215986365249075883171139954933/9332078728609550318939736328125:ℝ),(26863412048451933376224951785421458499007/9332078728609550318939736328125:ℝ),(984485335159565987767019760584131431553/1036897636512172257659970703125:ℝ)]]
theorem row064_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (984485335159565987767019760584131431553/15834458446647023475797545451520000000000:ℝ) row064_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row064_coefficients,Fin.sum_univ_succ]
 ring
theorem row064_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row064_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row064_coefficients]
#print axioms row064_identity
#print axioms row064_pos
end
end LewkoStage1Finite
