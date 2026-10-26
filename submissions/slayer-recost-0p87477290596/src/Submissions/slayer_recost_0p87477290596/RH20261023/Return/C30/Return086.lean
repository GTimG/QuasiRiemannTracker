/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row086_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6725206295333362167913677531552065288/1382185112879950924798828125:ℝ), (534010361560890664195389072472195285976/37318998047758674969568359375:ℝ), (523369026870503670594368861263893581824/37318998047758674969568359375:ℝ), (170939069444579561804597041518604058624/37318998047758674969568359375:ℝ)],
![(2662128177827092170923503933864361504/276437022575990184959765625:ℝ), (1056589275097360887160659391635759446752/37318998047758674969568359375:ℝ), (1035197748905447112170809239485100867584/37318998047758674969568359375:ℝ), (337995443968844709108090666421030223872/37318998047758674969568359375:ℝ)],
![(6589849721417902630861305536997753632/1382185112879950924798828125:ℝ), (522935537727376128293748085131696942176/37318998047758674969568359375:ℝ), (102436869663118298514899851639428104192/7463799609551734993913671875:ℝ), (167174585052549586025062760064382926848/37318998047758674969568359375:ℝ)]]
theorem row086_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (637720432481954902744532623536617/278270618289255824816996352000000000:ℝ) row086_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row086_coefficients,Fin.sum_univ_succ]
 ring
theorem row086_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row086_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row086_coefficients]
#print axioms row086_identity
#print axioms row086_pos
end
end RH20261023Return.C30
