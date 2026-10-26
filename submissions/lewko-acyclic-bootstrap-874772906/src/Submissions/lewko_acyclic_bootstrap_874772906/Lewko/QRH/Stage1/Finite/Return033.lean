/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row033_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13546178797440167447554468764563/1333222671053826105468750:ℝ),(39312134417558822999223202408571/1333222671053826105468750:ℝ),(19002669186215555818901466798944/666611335526913052734375:ℝ),(1223929541133202597025921557888/133322267105382610546875:ℝ)],
![(2524507254657953431769625692914/133322267105382610546875:ℝ),(36565143147204187614385407459818/666611335526913052734375:ℝ),(35282534476707941872248298573696/666611335526913052734375:ℝ),(11339836102718785104841988328448/666611335526913052734375:ℝ)],
![(5865461450603856208221572545126/666611335526913052734375:ℝ),(3391465474359597855840369679166/133322267105382610546875:ℝ),(16328314156026126078413081677952/666611335526913052734375:ℝ),(5236400306221416844072837077248/666611335526913052734375:ℝ)]]
theorem row033_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (20454688696177409547159519833/155331699502548529152000000000:ℝ) row033_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row033_coefficients,Fin.sum_univ_succ]
 ring
theorem row033_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row033_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_coefficients]
#print axioms row033_identity
#print axioms row033_pos
end
end LewkoStage1Finite
