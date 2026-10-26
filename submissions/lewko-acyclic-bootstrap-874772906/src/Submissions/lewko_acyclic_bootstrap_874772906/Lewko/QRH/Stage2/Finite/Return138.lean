/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row138_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8614928732210557457592139415899/38578690828283447003906250:ℝ),(4415538031964619211920438860471/7715738165656689400781250:ℝ),(9265427743134344030531477284192/19289345414141723501953125:ℝ),(2532898414093780492633098278464/19289345414141723501953125:ℝ)],
![(135311450891665960478388035114/296759160217564976953125:ℝ),(22442544846155962800779320765498/19289345414141723501953125:ℝ),(18728826568530080112717280533248/19289345414141723501953125:ℝ),(1015823881587348125527517660032/3857869082828344700390625:ℝ)],
![(4628847475191525735919294784438/19289345414141723501953125:ℝ),(11818655300978559647082740532134/19289345414141723501953125:ℝ),(9870296062404004742896492682176/19289345414141723501953125:ℝ),(535845524977181735209928136896/3857869082828344700390625:ℝ)]]
theorem row138_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (39576537720215320197392160601/17978973028425841655808000000000:ℝ) row138_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row138_coefficients,Fin.sum_univ_succ]
 ring
theorem row138_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row138_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row138_coefficients]
#print axioms row138_identity
#print axioms row138_pos
end
end LewkoStage2Finite
