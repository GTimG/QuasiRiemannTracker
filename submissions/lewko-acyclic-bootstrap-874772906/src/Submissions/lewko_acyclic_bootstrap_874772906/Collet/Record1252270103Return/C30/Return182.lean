/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row182_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10318079685961311295847152/1534318731658423828125:ℝ), (75720631504067547514156976/4602956194975271484375:ℝ), (60577342122230415537624784/4602956194975271484375:ℝ), (15810949676046801911009264/4602956194975271484375:ℝ)],
![(3350640017778014637248248/306863746331684765625:ℝ), (111804691907329715596780072/4602956194975271484375:ℝ), (77198388845001217389421184/4602956194975271484375:ℝ), (15653297204341721351364832/4602956194975271484375:ℝ)],
![(16353776080059084557776001/3068637463316847656250:ℝ), (102530131532107832583160867/9205912389950542968750:ℝ), (1252887767172340042213984/184118247799010859375:ℝ), (4587792533343211600433168/4602956194975271484375:ℝ)]]
theorem row182_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (286737033333950725027073/536283266122487808000000000:ℝ) row182_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row182_coefficients,Fin.sum_univ_succ]
 ring
theorem row182_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row182_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row182_coefficients]
#print axioms row182_identity
#print axioms row182_pos
end
end Record1252270103Return.C30
