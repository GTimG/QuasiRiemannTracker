/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![![(67434966674442449632634853437/10665781368430608843750000:ℝ),(37656332329569784591560336491/2133156273686121768750000:ℝ),(174809869426087795754781488879/10665781368430608843750000:ℝ),(17985612261722373003371553287/3555260456143536281250000:ℝ)],
![(48397783204937101713873685997/5332890684215304421875000:ℝ),(132197622484033088005829077831/5332890684215304421875000:ℝ),(119858428793341948928288247491/5332890684215304421875000:ℝ),(12016361004324885835694285219/1777630228071768140625000:ℝ)],
![(32883405404909643724578407957/10665781368430608843750000:ℝ),(4579945911138203293067509213/561356914127926781250000:ℝ),(76116574882920105979147536053/10665781368430608843750000:ℝ),(7322249408098976480522756321/3555260456143536281250000:ℝ)]]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7322249408098976480522756321/51777233167516176384000000000:ℝ) row003_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row003_coefficients,Fin.sum_univ_succ]
 ring
theorem row003_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row003_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]
#print axioms row003_identity
#print axioms row003_pos
end
end LewkoStage1Finite
