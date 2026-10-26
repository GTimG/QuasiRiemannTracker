/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2835270337315035743443936969/42663125473722435375000000:ℝ),(7456723798046388339504790027/42663125473722435375000000:ℝ),(6407636584147669448677769147/42663125473722435375000000:ℝ),(1786183123416316852616916089/42663125473722435375000000:ℝ)],
![(2019414518439838671796777573/21331562736861217687500000:ℝ),(4968034356020153269908602341/21331562736861217687500000:ℝ),(3963143051965225548113310263/21331562736861217687500000:ℝ),(202904642876982190000297099/4266312547372243537500000:ℝ)],
![(1374211201459531341649618177/42663125473722435375000000:ℝ),(620713283369243030959350719/8532625094744487075000000:ℝ),(2231867269014466098165323729/42663125473722435375000000:ℝ),(496174386113578865518188311/42663125473722435375000000:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (496174386113578865518188311/2427057804727320768000000000:ℝ) row001_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
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
end LewkoStage1Finite
