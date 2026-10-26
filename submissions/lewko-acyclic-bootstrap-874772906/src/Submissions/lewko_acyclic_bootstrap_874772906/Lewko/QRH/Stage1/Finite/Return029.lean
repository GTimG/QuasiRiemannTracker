/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row029_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4289941439659989066806740790485052155307/1866415745721910063787947265625:ℝ),(12741423387733770664944958873152646321921/1866415745721910063787947265625:ℝ),(12613553329169041024871555483075387777921/1866415745721910063787947265625:ℝ),(24339595013617005885329750879577740417/10914711963286023764841796875:ℝ)],
![(8271525097979509460425627014017592810454/1866415745721910063787947265625:ℝ),(24560421543375695834006909429625757683458/1866415745721910063787947265625:ℝ),(24307335455142420539263011035126210689954/1866415745721910063787947265625:ℝ),(280610243587905293227672130166860746/65316386551947858750234375:ℝ)],
![(3984268790356547841756982306381714020947/1866415745721910063787947265625:ℝ),(11827055417154326700942712455894548824657/1866415745721910063787947265625:ℝ),(11701841069015839903472123764815461222483/1866415745721910063787947265625:ℝ),(428783752929651981476625821839180713197/207379527302434451531994140625:ℝ)]]
theorem row029_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (428783752929651981476625821839180713197/3166891689329404695159509090304000000000:ℝ) row029_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row029_coefficients,Fin.sum_univ_succ]
 ring
theorem row029_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row029_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_coefficients]
#print axioms row029_identity
#print axioms row029_pos
end
end LewkoStage1Finite
