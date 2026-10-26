/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row028_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16948463245888589323297222329216848917/215610313502667389886119531250:ℝ),(5545530569294742726812225073123449479/23956701500296376654013281250:ℝ),(146945052783553366744767303224423899613/646830940508002169658358593750:ℝ),(48061064336360635527050393237741310431/646830940508002169658358593750:ℝ)],
![(79014950496480487296076560647140677833/539025783756668474715298828125:ℝ),(175706073097296429097012504711800817/407426896263543820646484375:ℝ),(683734432224156285754128034570959700409/1617077351270005424145896484375:ℝ),(44680320463490176269400592062248858247/323415470254001084829179296875:ℝ)],
![(73482866729460520791494785582193314721/1078051567513336949430597656250:ℝ),(14397049188864849151595157352423831333/71870104500889129962039843750:ℝ),(30214475101353147712355419336796050967/154007366787619564204371093750:ℝ),(13805671512083549756159223380681640299/215610313502667389886119531250:ℝ)]]
theorem row028_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (13805671512083549756159223380681640299/102893249463807072036284950118400000000:ℝ) row028_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row028_coefficients,Fin.sum_univ_succ]
 ring
theorem row028_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row028_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_coefficients]
#print axioms row028_identity
#print axioms row028_pos
end
end LewkoStage2Finite
