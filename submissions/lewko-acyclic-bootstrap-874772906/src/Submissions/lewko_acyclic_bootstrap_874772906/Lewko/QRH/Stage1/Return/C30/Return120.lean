/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def row120_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1426419043448959072292060644274511285248/37318998047758674969568359375:ℝ), (4237122736153992604758602262957749537792/37318998047758674969568359375:ℝ), (839033143592125814682849727848052686848/7463799609551734993913671875:ℝ), (1384461861577307417100019620557025181696/37318998047758674969568359375:ℝ)],
![(2820310464285348742761590494179046361344/37318998047758674969568359375:ℝ), (8376235154046795630021420861806946134272/37318998047758674969568359375:ℝ), (8291895814611233319441412063221218803712/37318998047758674969568359375:ℝ), (2735970795339548498646105745593319030784/37318998047758674969568359375:ℝ)],
![(1394841090281854772009887142789714162096/37318998047758674969568359375:ℝ), (828391486913382734448284892332187133936/7463799609551734993913671875:ℝ), (4099571128112609714678228565828169449472/37318998047758674969568359375:ℝ), (1352454617988516591318639206331947941888/37318998047758674969568359375:ℝ)]]
theorem row120_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2579602466561349089276579296745201/1113082473157023299267985408000000000:ℝ) row120_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row120_coefficients,Fin.sum_univ_succ]
 ring
theorem row120_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row120_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row120_coefficients]
#print axioms row120_identity
#print axioms row120_pos
end
end LewkoStage1Return.C30
