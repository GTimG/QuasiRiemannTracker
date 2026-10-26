/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row224_coefficients : Fin 3 → Fin 4 → ℝ := ![![(972443393185835878045302654282013/22995223610237261657613843750000:ℝ),(14678580664521246920123201652751417/206957012492135354918524593750000:ℝ),(3317078311425202686728815803359959/103478506246067677459262296875000:ℝ),(228216002175377362069724483753309/103478506246067677459262296875000:ℝ)],
![(748653800196180119532444052022329/5748805902559315414403460937500:ℝ),(12312819243253389152164767227041229/51739253123033838729631148437500:ℝ),(1344922522191960638299869162917903/10347850624606767745926229687500:ℝ),(982254574371417360724771805749247/51739253123033838729631148437500:ℝ)],
![(417017284715749358132701907254913/3832537268372876942935640625000:ℝ),(22795581660274731615889017380955857/103478506246067677459262296875000:ℝ),(14839352840284151092542960121817881/103478506246067677459262296875000:ℝ),(123200288288019805614712929469787/4139140249842707098370491875000:ℝ)]]
theorem row224_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (228216002175377362069724483753309/188376871815063647499172608000000000:ℝ) row224_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row224_coefficients,Fin.sum_univ_succ]
 ring
theorem row224_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row224_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row224_coefficients]
#print axioms row224_identity
#print axioms row224_pos
end
end LewkoStage1Finite
