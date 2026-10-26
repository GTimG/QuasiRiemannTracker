/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row034_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1530530141040754353087865177/4444146481595941406250:ℝ), (4316979473410440976335035089/4444146481595941406250:ℝ), (225047574030790140486452704/246897026755330078125:ℝ), (42144237474923144051861792/148138216053198046875:ℝ)],
![(1339777017972768984634036244/2222073240797970703125:ℝ), (1251556489909712726926533148/740691080265990234375:ℝ), (3498698609813446209782447456/2222073240797970703125:ℝ), (1083719020671431649324384256/2222073240797970703125:ℝ)],
![(21521998376454866556981784/82299008918443359375:ℝ), (1616115717063863503392058312/2222073240797970703125:ℝ), (298675951749283135258297984/444414648159594140625:ℝ), (458310468363754280312939776/2222073240797970703125:ℝ)]]
theorem row034_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1790275267045915157472421/16180643545437312000000000:ℝ) row034_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row034_coefficients,Fin.sum_univ_succ]
 ring
theorem row034_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row034_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_coefficients]
#print axioms row034_identity
#print axioms row034_pos
end
end LewkoStage1Return.C30
