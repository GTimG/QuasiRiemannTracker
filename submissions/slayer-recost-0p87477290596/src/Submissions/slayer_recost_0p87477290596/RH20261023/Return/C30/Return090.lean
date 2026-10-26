/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row090_coefficients : Fin 3 → Fin 4 → ℝ := ![![(63327385125708732598825500478858672/1492759921910346998782734375:ℝ), (4567763384346076497125543130152302304/37318998047758674969568359375:ℝ), (4388936778529191512746275812017486108/37318998047758674969568359375:ℝ), (156038582992554521091347729870738956/4146555338639852774396484375:ℝ)],
![(616394106707920647919339757269216768/7463799609551734993913671875:ℝ), (8874666626916463626330753217861306624/37318998047758674969568359375:ℝ), (8509489778816930789603280744567345728/37318998047758674969568359375:ℝ), (301863509118904086753164034783569216/4146555338639852774396484375:ℝ)],
![(302813210986270739548137683784775808/7463799609551734993913671875:ℝ), (870497700657181892582902478913572224/7463799609551734993913671875:ℝ), (833176944570683603009275522737617024/7463799609551734993913671875:ℝ), (29498909765274618406390080845424512/829311067727970554879296875:ℝ)]]
theorem row090_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (230460232541207956299922506604879/98940664280624293268265369600000000:ℝ) row090_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row090_coefficients,Fin.sum_univ_succ]
 ring
theorem row090_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row090_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_coefficients]
#print axioms row090_identity
#print axioms row090_pos
end
end RH20261023Return.C30
