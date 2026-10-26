/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6569587613769544568421765490133/44440754753150280140625000:ℝ),(418803087549760899546638051419/987572327847784003125000:ℝ),(18001262810060991685232905191007/44440754753150280140625000:ℝ),(381640390419360309779930557819/2962716983543352009375000:ℝ)],
![(5375737398453618034974002099573/22220377376575140070312500:ℝ),(5101842534587904799403509855061/7406792458858380023437500:ℝ),(4834394599056661875681456977069/7406792458858380023437500:ℝ),(4573261557108775354611593465597/22220377376575140070312500:ℝ)],
![(861880229552193262855663705609/8888150950630056028125000:ℝ),(810126844371273909942112092449/2962716983543352009375000:ℝ),(2279244591356786504076847664617/8888150950630056028125000:ℝ),(710711279107379559807112592879/8888150950630056028125000:ℝ)]]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (710711279107379559807112592879/4142178564981271835443200000000:ℝ) row004_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row004_coefficients,Fin.sum_univ_succ]
 ring
theorem row004_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row004_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_coefficients]
#print axioms row004_identity
#print axioms row004_pos
end
end LewkoStage2Finite
