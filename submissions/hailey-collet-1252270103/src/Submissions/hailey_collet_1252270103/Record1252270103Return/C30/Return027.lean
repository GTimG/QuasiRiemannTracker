/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row027_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13486740448087512295774723403/4444146481595941406250:ℝ), (13094567428156079476213207403/1481382160531980468750:ℝ), (38123280673777086078241199209/4444146481595941406250:ℝ), (4108750941408472162521266801/1481382160531980468750:ℝ)],
![(11855403324153395924969619739/2222073240797970703125:ℝ), (34427968711522286203970412833/2222073240797970703125:ℝ), (33306297237459845570179947949/2222073240797970703125:ℝ), (715577282373527832505693657/148138216053198046875:ℝ)],
![(137725044528126839697853177/59255286421279218750:ℝ), (29889691219981250600302723057/4444146481595941406250:ℝ), (28808223038845169539287829339/4444146481595941406250:ℝ), (3082610094178863444123656519/1481382160531980468750:ℝ)]]
theorem row027_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3082610094178863444123656519/22091971987370409984000000000:ℝ) row027_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row027_coefficients,Fin.sum_univ_succ]
 ring
theorem row027_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row027_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_coefficients]
#print axioms row027_identity
#print axioms row027_pos
end
end Record1252270103Return.C30
