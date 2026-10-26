/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1656758996177566870316072033/5332890684215304421875000:ℝ),(4460743394766511175872165631/5332890684215304421875000:ℝ),(7976103621850958388352565861/10665781368430608843750000:ℝ),(473310081558903784473075733/2133156273686121768750000:ℝ)],
![(1011555679197259540168912637/2666445342107652210937500:ℝ),(640176112427270280773875541/666611335526913052734375:ℝ),(2139096407865589776522992377/2666445342107652210937500:ℝ),(11767264409504346774428057/53328906842153044218750:ℝ)],
![(537004864111841951521753241/5332890684215304421875000:ℝ),(1228755008920134159811008167/5332890684215304421875000:ℝ),(908545569960937254890989381/5332890684215304421875000:ℝ),(42725318279108667370346891/1066578136843060884375000:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (42725318279108667370346891/485411560945464153600000000:ℝ) row002_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ]
 ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
#print axioms row002_identity
#print axioms row002_pos
end
end LewkoStage1Finite
