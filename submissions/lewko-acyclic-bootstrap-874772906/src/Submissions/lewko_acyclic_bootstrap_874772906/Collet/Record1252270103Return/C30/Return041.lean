/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row041_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3408442015778540368019964602/2222073240797970703125:ℝ), (9949950354469378134697364098/2222073240797970703125:ℝ), (1935657989331175277438159083/444414648159594140625:ℝ), (348529228079643107267981491/246897026755330078125:ℝ)],
![(18308703631075025699460559316/6666219722393912109375:ℝ), (53304730077449942563583614124/6666219722393912109375:ℝ), (689425078624909235694644744/88882929631918828125:ℝ), (1856747860982030160625727888/740691080265990234375:ℝ)],
![(1634770015288818221635810522/1333243944478782421875:ℝ), (4745018891328195892130434366/1333243944478782421875:ℝ), (509800547339233685906586074/148138216053198046875:ℝ), (164215811709487964896766758/148138216053198046875:ℝ)]]
theorem row041_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (82107905854743982448383379/1104598599368520499200000000:ℝ) row041_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row041_coefficients,Fin.sum_univ_succ]
 ring
theorem row041_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row041_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_coefficients]
#print axioms row041_identity
#print axioms row041_pos
end
end Record1252270103Return.C30
