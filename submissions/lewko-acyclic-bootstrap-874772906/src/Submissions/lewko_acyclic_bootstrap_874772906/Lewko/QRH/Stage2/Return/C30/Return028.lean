/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row028_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1972689479480921375341690235727409/25288200993919306288359375:ℝ), (5807903020752266612374805898210067/25288200993919306288359375:ℝ), (1899544433398894509459122334805969/8429400331306435429453125:ℝ), (207046405167096455632694593548361/2809800110435478476484375:ℝ)],
![(91963317534753396218727414664629842/632205024847982657208984375:ℝ), (270491623880266869097779554720311094/632205024847982657208984375:ℝ), (265138596809290152476221069757538662/632205024847982657208984375:ℝ), (17322035912329898917608785940371482/126441004969596531441796875:ℝ)],
![(42760005663423604654372754825615617/632205024847982657208984375:ℝ), (125636073652481867030284739666124619/632205024847982657208984375:ℝ), (123015009398079274213831615094599937/632205024847982657208984375:ℝ), (8027776637080847941625801050818187/126441004969596531441796875:ℝ)]]
theorem row028_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (8027776637080847941625801050818187/60339997913087841873061478400000000:ℝ) row028_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row028_coefficients,Fin.sum_univ_succ]
 ring
theorem row028_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row028_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_coefficients]
#print axioms row028_identity
#print axioms row028_pos
end
end LewkoStage2Return.C30
