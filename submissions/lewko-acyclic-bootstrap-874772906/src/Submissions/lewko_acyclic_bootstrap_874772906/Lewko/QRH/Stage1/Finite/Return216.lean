/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row216_coefficients : Fin 3 → Fin 4 → ℝ := ![![(78985030355954017195453920980947801/2586962656151691936481557421875:ℝ),(181333308461874199553910268616234003/2586962656151691936481557421875:ℝ),(129123033862199605553807032188233353/2586962656151691936481557421875:ℝ),(8913291988544487054394547403065717/862320885383897312160519140625:ℝ)],
![(49841831670419704519257310341824518/680779646355708404337251953125:ℝ),(2221232260631415845469243599003227118/12934813280758459682407787109375:ℝ),(327733045554123516399473523674319632/2586962656151691936481557421875:ℝ),(6386738441755623509476762282136612/226926548785236134779083984375:ℝ)],
![(649402177034620028825819232960399467/12934813280758459682407787109375:ℝ),(1600630006380386603577363568922222443/12934813280758459682407787109375:ℝ),(509326992445039145241505719804287657/5173925312303383872963114843750:ℝ),(214585752688948812038406238246139111/8623208853838973121605191406250:ℝ)]]
theorem row216_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (8913291988544487054394547403065717/12859861115908345002610183372800000000:ℝ) row216_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row216_coefficients,Fin.sum_univ_succ]
 ring
theorem row216_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row216_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row216_coefficients]
#print axioms row216_identity
#print axioms row216_pos
end
end LewkoStage1Finite
