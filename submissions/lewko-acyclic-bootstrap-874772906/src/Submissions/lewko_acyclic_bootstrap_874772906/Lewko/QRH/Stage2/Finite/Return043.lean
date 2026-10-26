/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row043_coefficients : Fin 3 → Fin 4 → ℝ := ![![(374660153908332086547421341293/1852820152954101562500:ℝ),(1854007469294060941654683754699/3088033588256835937500:ℝ),(458698703740354375862172869704/772008397064208984375:ℝ),(453915701635932529529782469704/2316025191192626953125:ℝ)],
![(2423455591100686486109054395439/6176067176513671875000:ℝ),(21579586790229857072399452155277/18528201529541015625000:ℝ),(533726517735360715277125876336/463205038238525390625:ℝ),(19555113034685086102813183568/51467226470947265625:ℝ)],
![(28208774089076381948998273431209/148225612236328125000000:ℝ),(16740062102422567652914776661333/29645122447265625000000:ℝ),(1293411386474797281708164156456/2316025191192626953125:ℝ),(426356129864852651777295252152/2316025191192626953125:ℝ)]]
theorem row043_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (53294516233106581472161906519/552625136271360000000000000000:ℝ) row043_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row043_coefficients,Fin.sum_univ_succ]
 ring
theorem row043_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row043_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_coefficients]
#print axioms row043_identity
#print axioms row043_pos
end
end LewkoStage2Finite
