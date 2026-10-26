/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row096_coefficients : Fin 3 → Fin 4 → ℝ := ![![(107210837743668718994207161793/30862952662626757603125000:ℝ),(262870051493142186487514217419/30862952662626757603125000:ℝ),(209631962917076392445450834209/30862952662626757603125000:ℝ),(53868566379911837705581278583/30862952662626757603125000:ℝ)],
![(593462350084716556364449400509/77157381656566894007812500:ℝ),(1432725677569354588620703533799/77157381656566894007812500:ℝ),(1117570444102054518565388131451/77157381656566894007812500:ℝ),(277682019891269962829758998161/77157381656566894007812500:ℝ)],
![(818448472015286793795904072717/154314763313133788015625000:ℝ),(2034934991373034543278293694151/154314763313133788015625000:ℝ),(1652763814057249859708549436863/154314763313133788015625000:ℝ),(435527178628126282050909815429/154314763313133788015625000:ℝ)]]
theorem row096_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (53868566379911837705581278583/14383178422740673324646400000000:ℝ) row096_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row096_coefficients,Fin.sum_univ_succ]
 ring
theorem row096_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row096_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row096_coefficients]
#print axioms row096_identity
#print axioms row096_pos
end
end LewkoStage2Finite
