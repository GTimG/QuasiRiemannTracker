/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row076_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1420752531751045170741860518123/19289345414141723501953125:ℝ),(772429734892252822156019500927/3857869082828344700390625:ℝ),(6967447467764386514789094903893/38578690828283447003906250:ℝ),(53441878001379480291385712971/989197200725216589843750:ℝ)],
![(2575849873978642348852535033186/19289345414141723501953125:ℝ),(6855810477472189926848617419694/19289345414141723501953125:ℝ),(241264714238010843514430849828/771573816565668940078125:ℝ),(583729476637371205751719203064/6429781804713907833984375:ℝ)],
![(260920662594548544605994545417/3857869082828344700390625:ℝ),(686709460228963875160569639331/3857869082828344700390625:ℝ),(595868757473007031216512027161/3857869082828344700390625:ℝ),(4359688934480670693298863673/98919720072521658984375:ℝ)]]
theorem row076_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4359688934480670693298863673/1475197786947761366630400000000:ℝ) row076_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row076_coefficients,Fin.sum_univ_succ]
 ring
theorem row076_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row076_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_coefficients]
#print axioms row076_identity
#print axioms row076_pos
end
end LewkoStage2Finite
