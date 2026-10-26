/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row080_coefficients : Fin 3 → Fin 4 → ℝ := ![![(230030775178090406278235616383719735466/5400727842363000016521919921875:ℝ),(666833022005310720025609461762526620842/5400727842363000016521919921875:ℝ),(643958926575846454740608572120119637504/5400727842363000016521919921875:ℝ),(207155253486262650008829286116312752128/5400727842363000016521919921875:ℝ)],
![(438652606689369715949804335616003742232/5400727842363000016521919921875:ℝ),(1268519804830976389555563662386600135192/5400727842363000016521919921875:ℝ),(1221871401166614127689841414359963256832/5400727842363000016521919921875:ℝ),(392001273405017580710708750089366863872/5400727842363000016521919921875:ℝ)],
![(210780808036289272618546285884644553512/5400727842363000016521919921875:ℝ),(608127183953454017614190132018757296936/5400727842363000016521919921875:ℝ),(584316584686018856356781840891793332224/5400727842363000016521919921875:ℝ),(7478748174775994082451905290307223552/216029113694520000660876796875:ℝ)]]
theorem row080_identity (δ p : ℝ) : rowMargin .oldSwitch .weakC7 δ p =
 Record12518109.Bernstein.bsum 2 3 (456466563401855107571527422504103/201353727930084448189315153920000000:ℝ) row080_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row080_coefficients,Fin.sum_univ_succ]
 ring
theorem row080_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .weakC7 δ p := by
 rw [row080_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_coefficients]
#print axioms row080_identity
#print axioms row080_pos
end
end LewkoStage2Finite
