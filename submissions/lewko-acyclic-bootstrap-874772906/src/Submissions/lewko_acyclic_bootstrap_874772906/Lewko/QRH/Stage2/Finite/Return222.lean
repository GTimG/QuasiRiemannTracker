/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row222_coefficients : Fin 3 → Fin 4 → ℝ := ![![(372134539692723723321511753033856807/4042128083939321340647144531250:ℝ),(154610180584818463252978777366111603/808425616787864268129428906250:ℝ),(226130236620460327235204888535455456/2021064041969660670323572265625:ℝ),(25551883246135830021843769629292352/2021064041969660670323572265625:ℝ)],
![(86188220395404864000156905840200426/404212808393932134064714453125:ℝ),(929731652204147233382006472476207714/2021064041969660670323572265625:ℝ),(590169968538338683562980391126558464/2021064041969660670323572265625:ℝ),(18225525972908212773175667776520576/404212808393932134064714453125:ℝ)],
![(259175997229407839827450023067661134/2021064041969660670323572265625:ℝ),(585227435158588357183898390950289662/2021064041969660670323572265625:ℝ),(405196204801915995885814649380799168/2021064041969660670323572265625:ℝ),(15802575537276412187066768693384128/404212808393932134064714453125:ℝ)]]
theorem row222_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (399248175720872344091308900457693/1883768221219892361817964544000000000:ℝ) row222_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row222_coefficients,Fin.sum_univ_succ]
 ring
theorem row222_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row222_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row222_coefficients]
#print axioms row222_identity
#print axioms row222_pos
end
end LewkoStage2Finite
