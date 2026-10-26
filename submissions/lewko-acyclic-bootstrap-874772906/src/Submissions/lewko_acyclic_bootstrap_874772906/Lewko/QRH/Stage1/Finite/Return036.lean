/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row036_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6338778713347301527170624781/213315627368612176875000000:ℝ),(16671058580353731912365001623/213315627368612176875000000:ℝ),(14325781020665559243218128903/213315627368612176875000000:ℝ),(16434161126169254559768527/877842087936675625000000:ℝ)],
![(4258410573298788169912684057/106657813684306088437500000:ℝ),(10569705811701342075339984089/106657813684306088437500000:ℝ),(8518660759511874362574107507/106657813684306088437500000:ℝ),(88294620844372818285872299/4266312547372243537500000:ℝ)],
![(3031304942724723520154743333/213315627368612176875000000:ℝ),(1365249063541751161503348571/42663125473722435375000000:ℝ),(547303277346033409841401229/23701736374290241875000000:ℝ),(1108802810559251303710611539/213315627368612176875000000:ℝ)]]
theorem row036_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1108802810559251303710611539/12135289023636603840000000000:ℝ) row036_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row036_coefficients,Fin.sum_univ_succ]
 ring
theorem row036_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row036_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_coefficients]
#print axioms row036_identity
#print axioms row036_pos
end
end LewkoStage1Finite
