/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row089_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19768842742332892903574567241404043992/4146555338639852774396484375:ℝ), (522803520697203381893543257632516702104/37318998047758674969568359375:ℝ), (511940480743505395395228042987306471424/37318998047758674969568359375:ℝ), (167056374524265147303493624902426165248/37318998047758674969568359375:ℝ)],
![(39171351911461642693409189092197255616/4146555338639852774396484375:ℝ), (1035602090133609943870878825828933404608/37318998047758674969568359375:ℝ), (1013763161774042765764763122835659587584/37318998047758674969568359375:ℝ), (66140579248270726998432074767300296704/7463799609551734993913671875:ℝ)],
![(19415754551976161622307012048477245824/4146555338639852774396484375:ℝ), (513155193627312467305813334164549483904/37318998047758674969568359375:ℝ), (100435661462237084273518791964857270272/7463799609551734993913671875:ℝ), (163764732245372926410235884096032079872/37318998047758674969568359375:ℝ)]]
theorem row089_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (156178219075558592233882793518097/69567654572313956204249088000000000:ℝ) row089_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row089_coefficients,Fin.sum_univ_succ]
 ring
theorem row089_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row089_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row089_coefficients]
#print axioms row089_identity
#print axioms row089_pos
end
end LewkoStage2Return.C30
