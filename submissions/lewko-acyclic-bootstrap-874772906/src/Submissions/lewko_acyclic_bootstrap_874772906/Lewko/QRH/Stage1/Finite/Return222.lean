/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row222_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2381720943749574338298783760842556619/25869626561516919364815574218750:ℝ),(52081049211686973185665634061711469/272311858542283361734900781250:ℝ),(1447317612543630638006993003449349984/12934813280758459682407787109375:ℝ),(163559147479543118027983982259646016/12934813280758459682407787109375:ℝ)],
![(2758079442160086162782166053489002442/12934813280758459682407787109375:ℝ),(5950446041970133728869070714602159738/12934813280758459682407787109375:ℝ),(755449127948527139750472972356347136/2586962656151691936481557421875:ℝ),(583267593604744686779342844387328384/12934813280758459682407787109375:ℝ)],
![(331750577593363795493225258280226334/2586962656151691936481557421875:ℝ),(3745532287851144096674633964591022438/12934813280758459682407787109375:ℝ),(2593329636823673387121541223012290496/12934813280758459682407787109375:ℝ),(505706146005715986734591125103649728/12934813280758459682407787109375:ℝ)]]
theorem row222_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2555611679367861219187249722806969/12056119796164073439947046912000000000:ℝ) row222_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row222_coefficients,Fin.sum_univ_succ]
 ring
theorem row222_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row222_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row222_coefficients]
#print axioms row222_identity
#print axioms row222_pos
end
end LewkoStage1Finite
