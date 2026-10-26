/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row126_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5901326447002205894886059428288380848/37318998047758674969568359375:ℝ), (3400079838017147982307725972567001072/7463799609551734993913671875:ℝ), (16308545311511524302816602291313995776/37318998047758674969568359375:ℝ), (5209429466856619723087069356767371264/37318998047758674969568359375:ℝ)],
![(11618807070412722592040553207334405168/37318998047758674969568359375:ℝ), (33434490995104249108466407589151124528/37318998047758674969568359375:ℝ), (32036290682303017384127917742574129152/37318998047758674969568359375:ℝ), (10220519449300253060443600860757409792/37318998047758674969568359375:ℝ)],
![(1146501445542145686897140134574931004/7463799609551734993913671875:ℝ), (16478919708254100882725646408149677868/37318998047758674969568359375:ℝ), (15772322992846841310237609759509656576/37318998047758674969568359375:ℝ), (5025866298479188177552673399234633728/37318998047758674969568359375:ℝ)]]
theorem row126_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (613509069638572775580160327055009/278270618289255824816996352000000000:ℝ) row126_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row126_coefficients,Fin.sum_univ_succ]
 ring
theorem row126_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row126_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row126_coefficients]
#print axioms row126_identity
#print axioms row126_pos
end
end RH20261023Return.C30
