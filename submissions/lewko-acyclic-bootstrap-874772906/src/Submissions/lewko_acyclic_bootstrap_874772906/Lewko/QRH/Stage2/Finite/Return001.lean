/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(23627251897229513440024032157/355526038025202241125000000:ℝ),(20713120858766265855498194317/118508679341734080375000000:ℝ),(17798989820303018270972356477/118508679341734080375000000:ℝ),(14884858781839770686446518637/355526038025202241125000000:ℝ)],
![(16828453597239123939989151073/177763019012601120562500000:ℝ),(13800094808792904478118403439/59254339670867040187500000:ℝ),(6605238105233991188781253111/35552603802520224112500000:ℝ),(939373299670040716615578479/19751446556955680062500000:ℝ)],
![(11451759449349543404454269989/355526038025202241125000000:ℝ),(1724203469682737766395068289/23701735868346816075000000:ℝ),(18598892761632548011412803309/355526038025202241125000000:ℝ),(4134786265295461241441048963/355526038025202241125000000:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4134786265295461241441048963/20225481274322616384000000000:ℝ) row001_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ]
 ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
#print axioms row001_identity
#print axioms row001_pos
end
end LewkoStage2Finite
