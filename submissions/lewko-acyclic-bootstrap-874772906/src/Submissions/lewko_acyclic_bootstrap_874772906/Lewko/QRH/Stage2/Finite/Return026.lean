/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row026_coefficients : Fin 3 → Fin 4 → ℝ := ![![(438607228377330666799890152417/3703396229429190011718750:ℝ),(1251129953655842809257730940801/3703396229429190011718750:ℝ),(7128939867542468791172664112981/22220377376575140070312500:ℝ),(2253720994151949743177963132677/22220377376575140070312500:ℝ)],
![(349745874152943023408583188123/1851698114714595005859375:ℝ),(988327875472958996834493592597/1851698114714595005859375:ℝ),(557545944734944223784259780892/1111018868828757003515625:ℝ),(871934206683005482694973941038/5555094344143785017578125:ℝ)],
![(54302136729432322882656575083/740679245885838002343750:ℝ),(50518310918121236362468941683/246893081961946000781250:ℝ),(702923018901482026712788721783/3703396229429190011718750:ℝ),(216639233564158009309599971953/3703396229429190011718750:ℝ)]]
theorem row026_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (216639233564158009309599971953/1725907735408863264768000000000:ℝ) row026_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row026_coefficients,Fin.sum_univ_succ]
 ring
theorem row026_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row026_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_coefficients]
#print axioms row026_identity
#print axioms row026_pos
end
end LewkoStage2Finite
