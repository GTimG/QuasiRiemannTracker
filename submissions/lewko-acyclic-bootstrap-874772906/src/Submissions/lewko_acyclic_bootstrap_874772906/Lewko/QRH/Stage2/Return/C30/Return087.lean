/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row087_coefficients : Fin 3 → Fin 4 → ℝ := ![![(46695205985341562433637168898211102896/37318998047758674969568359375:ℝ), (137329369370849654589314925763070692784/37318998047758674969568359375:ℝ), (26919204374011764223223660162829849416/7463799609551734993913671875:ℝ), (43961816481063441638204628324289657192/37318998047758674969568359375:ℝ)],
![(91679219713146223488122502301225262368/37318998047758674969568359375:ℝ), (269468097589240300765075740282601956064/37318998047758674969568359375:ℝ), (263944886411149854494330616093050954624/37318998047758674969568359375:ℝ), (86155923437081532772327990611674260928/37318998047758674969568359375:ℝ)],
![(45104226562206354953134988553643205072/37318998047758674969568359375:ℝ), (26499671816587110753385354394561813296/7463799609551734993913671875:ℝ), (129707491023945367003243619985706772944/37318998047758674969568359375:ℝ), (42313315401644797626374874066540911536/37318998047758674969568359375:ℝ)]]
theorem row087_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2644582212602799851648429629158806971/1139796452512791858450417057792000000000:ℝ) row087_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row087_coefficients,Fin.sum_univ_succ]
 ring
theorem row087_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row087_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row087_coefficients]
#print axioms row087_identity
#print axioms row087_pos
end
end LewkoStage2Return.C30
