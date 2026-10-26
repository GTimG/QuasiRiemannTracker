/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row061_coefficients : Fin 3 → Fin 4 → ℝ := ![![(350082047407239789380360000863/6666113355269130527343750:ℝ),(997329635773698497143096667839/6666113355269130527343750:ℝ),(630674970165801539413306716851/4444075570179420351562500:ℝ),(199165126718073329499867688867/4444075570179420351562500:ℝ)],
![(287231763041070890707288644901/3333056677634565263671875:ℝ),(810233474283580073469249183307/3333056677634565263671875:ℝ),(760536369695571539664816331036/3333056677634565263671875:ℝ),(47502809257380405674789908526/666611335526913052734375:ℝ)],
![(235986255976714947023164355689/6666113355269130527343750:ℝ),(26305929052951031900952034747/266644534210765221093750:ℝ),(609269959992148966129970719433/6666113355269130527343750:ℝ),(187583255045695721394646706447/6666113355269130527343750:ℝ)]]
theorem row061_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (187583255045695721394646706447/3106633990050970583040000000000:ℝ) row061_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row061_coefficients,Fin.sum_univ_succ]
 ring
theorem row061_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row061_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_coefficients]
#print axioms row061_identity
#print axioms row061_pos
end
end LewkoStage1Finite
