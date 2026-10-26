/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row095_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22028031802914299969883143300551267835278/36725025273689068814410716796875:ℝ),(63248457877709217304452455289846145493902/36725025273689068814410716796875:ℝ),(483684864504487628789717193176071854592/293800202189512550515285734375:ℝ),(19240002886822088411492516001464104165376/36725025273689068814410716796875:ℝ)],
![(43796299672076319803984165731952524423808/36725025273689068814410716796875:ℝ),(125687151076187281921826005911955276460672/36725025273689068814410716796875:ℝ),(24016307260976102530758271669749177319424/7345005054737813762882143359375:ℝ),(38190324445033303285327488168743134560256/36725025273689068814410716796875:ℝ)],
![(4356587259840330471126057874242902595584/7345005054737813762882143359375:ℝ),(12496490017694791723431899472144321124352/7345005054737813762882143359375:ℝ),(11932887669840739823081462443895149821952/7345005054737813762882143359375:ℝ),(3792948639710932935492900845993731293184/7345005054737813762882143359375:ℝ)]]
theorem row095_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (904309425285084947465157710550721/427877556682042100234883686400000000:ℝ) row095_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row095_coefficients,Fin.sum_univ_succ]
 ring
theorem row095_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row095_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row095_coefficients]
#print axioms row095_identity
#print axioms row095_pos
end
end LewkoStage1Finite
