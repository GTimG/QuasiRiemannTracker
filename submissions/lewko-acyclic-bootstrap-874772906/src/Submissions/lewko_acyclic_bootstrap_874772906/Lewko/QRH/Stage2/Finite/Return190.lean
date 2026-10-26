/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row190_coefficients : Fin 3 → Fin 4 → ℝ := ![![(451895785263139513745948067882577/129348098686058282900708625000000:ℝ),(1211587046202989370993669388763011/129348098686058282900708625000000:ℝ),(1067486736616560200749494573878291/129348098686058282900708625000000:ℝ),(307795475676710343501773252997857/129348098686058282900708625000000:ℝ)],
![(71278262464082113453372401184453/64674049343029141450354312500000:ℝ),(180989862706779649923869200680337/64674049343029141450354312500000:ℝ),(32296762695331055094807651382771/12934809868605828290070862500000:ℝ),(51772213233957739003541457417971/64674049343029141450354312500000:ℝ)],
![(208053134409257844763631234486329/129348098686058282900708625000000:ℝ),(56305089489099841892589673797887/25869619737211656580141725000000:ℝ),(96616329174953691138566455928849/129348098686058282900708625000000:ℝ),(5704123728343057806860821425743/129348098686058282900708625000000:ℝ)]]
theorem row190_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5704123728343057806860821425743/7358469614140204538351424000000000:ℝ) row190_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row190_coefficients,Fin.sum_univ_succ]
 ring
theorem row190_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row190_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row190_coefficients]
#print axioms row190_identity
#print axioms row190_pos
end
end LewkoStage2Finite
