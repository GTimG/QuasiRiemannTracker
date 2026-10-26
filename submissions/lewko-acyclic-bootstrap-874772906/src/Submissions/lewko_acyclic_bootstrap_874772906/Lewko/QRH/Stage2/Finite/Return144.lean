/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row144_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172026939066297893276971505766038501/95044546360359502480411875000000:ℝ),(10399239501899464653584017843772531831/2376113659008987562010296875000000:ℝ),(8174709122441992300510668053564897887/2376113659008987562010296875000000:ℝ),(2071012429701067145074441785193328581/2376113659008987562010296875000000:ℝ)],
![(3551791523139048731139487822353231509/1188056829504493781005148437500000:ℝ),(1514520298785531044785420170135690331/237611365900898756201029687500000:ℝ),(4829912025789216759628874573114600533/1188056829504493781005148437500000:ℝ),(802688720626975474620641458851880387/1188056829504493781005148437500000:ℝ)],
![(5319127106425322192394612568914589943/2376113659008987562010296875000000:ℝ),(11995638112577614539542158862849060579/2376113659008987562010296875000000:ℝ),(16898674884090646938780718924268405783/4752227318017975124020593750000000:ℝ),(3529619535851975263934076121555714511/4752227318017975124020593750000000:ℝ)]]
theorem row144_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (802688720626975474620641458851880387/1107349224937336951921115136000000000000:ℝ) row144_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row144_coefficients,Fin.sum_univ_succ]
 ring
theorem row144_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row144_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row144_coefficients]
#print axioms row144_identity
#print axioms row144_pos
end
end LewkoStage2Finite
