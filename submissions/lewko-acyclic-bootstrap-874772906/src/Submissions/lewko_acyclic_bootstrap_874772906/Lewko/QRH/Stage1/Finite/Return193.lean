/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row193_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10177727474068110953395367810707783/5173925312303383872963114843750:ℝ),(124920214144092476899075116938310857/25869626561516919364815574218750:ℝ),(100207736116409229557213617099113889/25869626561516919364815574218750:ℝ),(26120351677623768173648071464341947/25869626561516919364815574218750:ℝ)],
![(41997212032625162375104381436841803/12934813280758459682407787109375:ℝ),(18393355770818199094635769076146837/2586962656151691936481557421875:ℝ),(61648077447429731471215990170940411/12934813280758459682407787109375:ℝ),(11608751044671974308807441539548029/12934813280758459682407787109375:ℝ)],
![(60545480794072997819401909144139081/25869626561516919364815574218750:ℝ),(138082459807848725615800081153639493/25869626561516919364815574218750:ℝ),(198108921342429491110165149652495361/51739253123033838729631148437500:ℝ),(42860564361648225356533593914744537/51739253123033838729631148437500:ℝ)]]
theorem row193_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (11608751044671974308807441539548029/12056119796164073439947046912000000000:ℝ) row193_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
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
end LewkoStage1Finite
