/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row100_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1445107018343123181468124567487431424/37318998047758674969568359375:ℝ), (4151789150488025014220657002906518272/37318998047758674969568359375:ℝ), (3971329121837827401721358384674742272/37318998047758674969568359375:ℝ), (1264635654631421147383825949255655424/37318998047758674969568359375:ℝ)],
![(2828344333490825238732880098010945984/37318998047758674969568359375:ℝ), (8110080414913618042731625301220710848/37318998047758674969568359375:ℝ), (7741413517426335650542661965821599744/37318998047758674969568359375:ℝ), (491930839825491756458933352522366976/7463799609551734993913671875:ℝ)],
![(279652783889582758919192484870429052/7463799609551734993913671875:ℝ), (4003119167661184714308836980147751276/37318998047758674969568359375:ℝ), (3814662017643856477747597889396380672/37318998047758674969568359375:ℝ), (1209794860531592475106982708600774656/37318998047758674969568359375:ℝ)]]
theorem row100_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (147680036685985409558957850170993/69567654572313956204249088000000000:ℝ) row100_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row100_coefficients,Fin.sum_univ_succ]
 ring
theorem row100_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row100_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row100_coefficients]
#print axioms row100_identity
#print axioms row100_pos
end
end LewkoStage2Return.C30
