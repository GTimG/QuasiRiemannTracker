/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row011_coefficients : Fin 3 → Fin 4 → ℝ := ![![(52879031882932931780848309921951688/632205024847982657208984375:ℝ), (155773267930266016435865302605073696/632205024847982657208984375:ℝ), (152931285717498008668566508579877878/632205024847982657208984375:ℝ), (10007400401731100567401778179351174/126441004969596531441796875:ℝ)],
![(98859057213451925318714330613820768/632205024847982657208984375:ℝ), (290958958476401689874519200217824736/632205024847982657208984375:ℝ), (285385013402646857390083795801381168/632205024847982657208984375:ℝ), (414600052443010039015128560877232/2809800110435478476484375:ℝ)],
![(9218790098918692539535723349208016/126441004969596531441796875:ℝ), (27105543196498149200355846002763248/126441004969596531441796875:ℝ), (8853064861622051047622883844600816/42147001656532177147265625:ℝ), (8672430925179345528798528880247216/126441004969596531441796875:ℝ)]]
theorem row011_identity (δ p : ℝ) : rowMargin .oldSmall .weakC2 δ p =
 Record12518109.Bernstein.bsum 2 3 (542026932823709095549908055015451/3771249869567990117066342400000000:ℝ) row011_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row011_coefficients,Fin.sum_univ_succ]
 ring
theorem row011_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .weakC2 δ p := by
 rw [row011_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_coefficients]
#print axioms row011_identity
#print axioms row011_pos
end
end Record1252270103Return.C30
