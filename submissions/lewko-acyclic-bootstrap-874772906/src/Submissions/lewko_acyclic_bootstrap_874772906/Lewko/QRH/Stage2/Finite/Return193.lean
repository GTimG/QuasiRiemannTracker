/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row193_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7951226090070590954556614870376863/4042128083939321340647144531250:ℝ),(19518429695582036675197659135735293/4042128083939321340647144531250:ℝ),(15657121439305892295048230845975861/4042128083939321340647144531250:ℝ),(4081197887589261940090992330617431/4042128083939321340647144531250:ℝ)],
![(6561961940865014713154487827950823/2021064041969660670323572265625:ℝ),(2873903599265499927105242190662809/404212808393932134064714453125:ℝ),(9632236692546602576005987845713911/2021064041969660670323572265625:ℝ),(1813780704327636860739021907850689/2021064041969660670323572265625:ℝ)],
![(9460147621233332214510164415989021/4042128083939321340647144531250:ℝ),(21575148576717239837686802097156713/4042128083939321340647144531250:ℝ),(30954077697047228884762752802272101/8084256167878642681294289062500:ℝ),(6696825954188211656171370408686717/8084256167878642681294289062500:ℝ)]]
theorem row193_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1813780704327636860739021907850689/1883768221219892361817964544000000000:ℝ) row193_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row193_coefficients,Fin.sum_univ_succ]
 ring
theorem row193_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row193_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row193_coefficients]
#print axioms row193_identity
#print axioms row193_pos
end
end LewkoStage2Finite
