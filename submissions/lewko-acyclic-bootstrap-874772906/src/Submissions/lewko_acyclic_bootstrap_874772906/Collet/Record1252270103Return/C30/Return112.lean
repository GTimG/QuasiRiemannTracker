/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row112_coefficients : Fin 3 → Fin 4 → ℝ := ![![(213187616174341929780331/93331334953125000:ℝ), (609358600033219223542177/93331334953125000:ℝ), (579932631010432470563561/93331334953125000:ℝ), (36752329430311035360343/18666266990625000:ℝ)],
![(198796137640542445317307/46665667476562500:ℝ), (564525012685421857708609/46665667476562500:ℝ), (533472402807659622232397/46665667476562500:ℝ), (33548705552556041968219/9333133495312500:ℝ)],
![(191071710451582029255283/93331334953125000:ℝ), (539543350316935620216241/93331334953125000:ℝ), (506716080753140663853683/93331334953125000:ℝ), (6329777635511482915709/3733253398125000:ℝ)]]
theorem row112_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (6329777635511482915709/1781577916958638080000000:ℝ) row112_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row112_coefficients,Fin.sum_univ_succ]
 ring
theorem row112_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row112_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row112_coefficients]
#print axioms row112_identity
#print axioms row112_pos
end
end Record1252270103Return.C30
