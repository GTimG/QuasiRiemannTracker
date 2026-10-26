/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row038_coefficients : Fin 3 → Fin 4 → ℝ := ![![(145207931611827527327566403/53329757779151296875000:ℝ), (80988347980649167966911589/10665951555830259375000:ℝ), (41732989818361893988422809/5925528642127921875000:ℝ), (476712381351870879172073/219464023782515625000:ℝ)],
![(106527345227756442801527443/26664878889575648437500:ℝ), (289975903799587142126692729/26664878889575648437500:ℝ), (87355458017018112382606343/8888292963191882812500:ℝ), (8731647596802497021961527/2962764321063960937500:ℝ)],
![(26692216859733264544808561/17776585926383765625000:ℝ), (7817059887574466814802519/1975176214042640625000:ℝ), (61324111986604029173994109/17776585926383765625000:ℝ), (24611291916550223253947/24793006870828125000:ℝ)]]
theorem row038_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (24611291916550223253947/361074332952576000000000:ℝ) row038_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row038_coefficients,Fin.sum_univ_succ]
 ring
theorem row038_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row038_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_coefficients]
#print axioms row038_identity
#print axioms row038_pos
end
end LewkoStage2Return.C30
