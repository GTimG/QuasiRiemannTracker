/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row107_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2932002712961464524951777013/209868080687323076531250000:ℝ),(6323329375520829247239178231/209868080687323076531250000:ℝ),(1093897751881081632757258007/52467020171830769132812500:ℝ),(95592662985118424411663081/20986808068732307653125000:ℝ)],
![(4328146512276826504567620637/104934040343661538265625000:ℝ),(8548776269944748504421547429/104934040343661538265625000:ℝ),(5108585382554633306172588707/104934040343661538265625000:ℝ),(166256038931831235413732383/20986808068732307653125000:ℝ)],
![(12440068893586526933183464261/209868080687323076531250000:ℝ),(1487261500022742724854772813/11045688457227530343750000:ℝ),(21077858256618859543436370731/209868080687323076531250000:ℝ),(54174818834928046798727911/2209137691445506068750000:ℝ)]]
theorem row107_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (166256038931831235413732383/19102659077672784921600000000:ℝ) row107_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row107_coefficients,Fin.sum_univ_succ]
 ring
theorem row107_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row107_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row107_coefficients]
#print axioms row107_identity
#print axioms row107_pos
end
end LewkoStage1Finite
