/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row068_coefficients : Fin 3 → Fin 4 → ℝ := ![![(30925618440287236693187787115487/6666113355269130527343750:ℝ),(89750328038507770764842533326439/6666113355269130527343750:ℝ),(43387451353377118740888290339296/3333056677634565263671875:ℝ),(310554334552123850897187917696/74067926169657005859375:ℝ)],
![(5816997817981107820941491389114/666611335526913052734375:ℝ),(84258076425762956793861587354002/3333056677634565263671875:ℝ),(81313485111780724821370949110144/3333056677634565263671875:ℝ),(26140080348564438072871662451712/3333056677634565263671875:ℝ)],
![(13666788819494321015673760598014/3333056677634565263671875:ℝ),(7903227245529672638877613281334/666611335526913052734375:ℝ),(12686217880118194529949521209216/1111018892544855087890625:ℝ),(12209139960726848094334414068992/3333056677634565263671875:ℝ)]]
theorem row068_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (47691952971589250368493804957/776658497512742645760000000000:ℝ) row068_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row068_coefficients,Fin.sum_univ_succ]
 ring
theorem row068_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row068_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_coefficients]
#print axioms row068_identity
#print axioms row068_pos
end
end LewkoStage1Finite
