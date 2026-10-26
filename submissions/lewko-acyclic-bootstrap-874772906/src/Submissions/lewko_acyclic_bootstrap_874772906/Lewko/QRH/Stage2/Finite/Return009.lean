/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![![(273078124510521057232765571/79053659859375000:ℝ),(162935579969991468869412487/15810731971875000:ℝ),(540085454944472948106967631/52702439906250000:ℝ),(1326066207789003136030393/390388443750000:ℝ)],
![(88003445398407498431650939/13175609976562500:ℝ),(262496985173282946839532757/13175609976562500:ℝ),(7249609086381872294978648/365989166015625:ℝ),(961026525943021713459439/146395666406250:ℝ)],
![(255084886419746866361157301/79053659859375000:ℝ),(760732090580916863248314631/79053659859375000:ℝ),(252072175032655796469042407/26351219953125000:ℝ),(9280345219881384908147033/2927913328125000:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (9280345219881384908147033/44712149297135616000000000:ℝ) row009_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ]
 ring
theorem row009_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
#print axioms row009_identity
#print axioms row009_pos
end
end LewkoStage2Finite
