/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row106_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5398004593801254338019353789/1234518106505070304125000000:ℝ),(14414159339618951971119848327/1234518106505070304125000000:ℝ),(12634304897834140928181635287/1234518106505070304125000000:ℝ),(3618150152016443295081140749/1234518106505070304125000000:ℝ)],
![(1486507304192495739697157921/617259053252535152062500000:ℝ),(3709969937285608694591098109/617259053252535152062500000:ℝ),(624088580063448449064846647/123451810650507030412500000:ℝ),(896980267224129290430293047/617259053252535152062500000:ℝ)],
![(2513082440604018357874962053/1234518106505070304125000000:ℝ),(780590738122941668306533459/246903621301014060825000000:ℝ),(1810602702794315817767629693/1234518106505070304125000000:ℝ),(254038992477886239609924451/1234518106505070304125000000:ℝ)]]
theorem row106_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (254038992477886239609924451/70230363392288443968000000000:ℝ) row106_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row106_coefficients,Fin.sum_univ_succ]
 ring
theorem row106_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row106_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row106_coefficients]
#print axioms row106_identity
#print axioms row106_pos
end
end LewkoStage2Finite
