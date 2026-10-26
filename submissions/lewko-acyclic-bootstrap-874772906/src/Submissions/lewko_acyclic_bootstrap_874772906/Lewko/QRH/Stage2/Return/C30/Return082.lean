/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row082_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1644415346675204047662552928721304778/37318998047758674969568359375:ℝ), (4758864325593838906453314583265635742/37318998047758674969568359375:ℝ), (36698462544742985556184443811476134/298551984382069399756546875:ℝ), (163649845475692288361314591321131754/4146555338639852774396484375:ℝ)],
![(3173871671535637158751275330747235796/37318998047758674969568359375:ℝ), (366627919519237751102707660414810396/1492759921910346998782734375:ℝ), (8815568412812936676778094711124956012/37318998047758674969568359375:ℝ), (313746788685132568552829559055770212/4146555338639852774396484375:ℝ)],
![(1544736474394901884203349546575193018/37318998047758674969568359375:ℝ), (4452418923102627204823679233963480958/37318998047758674969568359375:ℝ), (4273592317285742220444411915828664762/37318998047758674969568359375:ℝ), (151766565909463806561649067048930758/4146555338639852774396484375:ℝ)]]
theorem row082_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (75883282954731903280824533524465379/31661012569799773845844918272000000000:ℝ) row082_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row082_coefficients,Fin.sum_univ_succ]
 ring
theorem row082_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row082_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row082_coefficients]
#print axioms row082_identity
#print axioms row082_pos
end
end LewkoStage2Return.C30
