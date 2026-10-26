/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row134_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1537487604378958391176769490491522122/37318998047758674969568359375:ℝ), (4422753151628723543222755609270790366/37318998047758674969568359375:ℝ), (4236149371196232095354620828391014366/37318998047758674969568359375:ℝ), (150096943209440280191514967734638458/4146555338639852774396484375:ℝ)],
![(3021136785081020938238217032484718484/37318998047758674969568359375:ℝ), (8675816682912802385943782789815996348/37318998047758674969568359375:ℝ), (8294578409282369431198716139590853244/37318998047758674969568359375:ℝ), (58663894990544531538753341827990564/829311067727970554879296875:ℝ)],
![(1498929330236531320176074686542458362/37318998047758674969568359375:ℝ), (4298648791999601176430329487404062782/37318998047758674969568359375:ℝ), (4103760760651816074033467992338064378/37318998047758674969568359375:ℝ), (144892154443305903872385840719606662/4146555338639852774396484375:ℝ)]]
theorem row134_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (72446077221652951936192920359803331/31661012569799773845844918272000000000:ℝ) row134_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row134_coefficients,Fin.sum_univ_succ]
 ring
theorem row134_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row134_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row134_coefficients]
#print axioms row134_identity
#print axioms row134_pos
end
end LewkoStage1Return.C30
