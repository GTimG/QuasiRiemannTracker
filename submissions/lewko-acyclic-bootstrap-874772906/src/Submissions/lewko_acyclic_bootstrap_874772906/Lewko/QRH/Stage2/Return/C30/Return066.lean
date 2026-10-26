/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row066_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2036052271168026658753152199375263388/1973634989010239080177734375:ℝ), (6048482185699221680126313540586129756/1973634989010239080177734375:ℝ), (1996359670166883363552849547543176566/657878329670079693392578125:ℝ), (61262936118861009958291195611922/61169533209677330859375:ℝ)],
![(3940175356072095466599552298858386856/1973634989010239080177734375:ℝ), (11701978362923820627593587767587873944/1973634989010239080177734375:ℝ), (772265300249078125155944797098329648/131575665934015938678515625:ℝ), (141562057413127669737792555101683616/73097592185564410376953125:ℝ)],
![(70581133295335443207412255364699084/73097592185564410376953125:ℝ), (1886063550442319058991907930544647396/657878329670079693392578125:ℝ), (1866528960882424332276268337226977324/657878329670079693392578125:ℝ), (68410605384588339604934244996069076/73097592185564410376953125:ℝ)]]
theorem row066_identity (δ p : ℝ) : rowMargin .oldPeak .P δ p =
 Record12518109.Bernstein.bsum 2 3 (17102651346147084901233561249017269/279068238091861605218254848000000000:ℝ) row066_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row066_coefficients,Fin.sum_univ_succ]
 ring
theorem row066_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .P δ p := by
 rw [row066_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row066_coefficients]
#print axioms row066_identity
#print axioms row066_pos
end
end LewkoStage2Return.C30
