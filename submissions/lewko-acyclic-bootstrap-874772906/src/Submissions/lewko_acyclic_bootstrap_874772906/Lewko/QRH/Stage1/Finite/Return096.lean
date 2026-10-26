/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row096_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3837017827958325465133444777/1104568845722753034375000:ℝ),(178751554174441352216684832889/20986808068732307653125000:ℝ),(142549665283854748979579749739/20986808068732307653125000:ℝ),(36630605552837136688867867613/20986808068732307653125000:ℝ)],
![(403554392755497749241209363039/52467020171830769132812500:ℝ),(974253493923493730363529572909/52467020171830769132812500:ℝ),(759947981062165730062092414601/52467020171830769132812500:ℝ),(188823814167463085470397204731/52467020171830769132812500:ℝ)],
![(556545090818429377262768082383/104934040343661538265625000:ℝ),(1383756219719065657275379547213/104934040343661538265625000:ℝ),(1123879852012959332079763765237/104934040343661538265625000:ℝ),(296158644240275055903902300407/104934040343661538265625000:ℝ)]]
theorem row096_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (36630605552837136688867867613/9780561447768465879859200000000:ℝ) row096_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
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
end LewkoStage1Finite
