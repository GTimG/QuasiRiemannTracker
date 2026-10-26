/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row011_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60934414592980130017161711606484/666611335526913052734375:ℝ),(179962272696975625033971027467968/666611335526913052734375:ℝ),(177139821069623883571766727386519/666611335526913052734375:ℝ),(11622385443444513250258858867507/133322267105382610546875:ℝ)],
![(113967222559663528983850990002224/666611335526913052734375:ℝ),(336312147439116201322033551080048/666611335526913052734375:ℝ),(330760250438419006953840006551224/666611335526913052734375:ℝ),(4336610011966584138002035318936/26664453421076522109375:ℝ)],
![(10632184914991356230378941219688/133322267105382610546875:ℝ),(31347011077608700444716566745464/133322267105382610546875:ℝ),(30801284057912098545764403661864/133322267105382610546875:ℝ),(10086449973210361577152403136088/133322267105382610546875:ℝ)]]
theorem row011_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1260806246651295197144050392011/7952983014530484692582400000000:ℝ) row011_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row011_coefficients,Fin.sum_univ_succ]
 ring
theorem row011_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row011_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_coefficients]
#print axioms row011_identity
#print axioms row011_pos
end
end LewkoStage1Finite
