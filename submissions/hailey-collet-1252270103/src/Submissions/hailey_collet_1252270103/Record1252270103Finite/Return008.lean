/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22237970809463077058936732227/49408548446777343750:ℝ), (21998998670888445300361596673/16469516148925781250:ℝ), (10880352463054143517778532272/8234758074462890625:ℝ), (2152308957512260226452313584/4940854844677734375:ℝ)],
![(28691238071219987428206006701/32939032297851562500:ℝ), (255363074965969282753822940167/98817096893554687500:ℝ), (2525132991831978333487410976/988170968935546875:ℝ), (2311776067524680913320449376/2744919358154296875:ℝ)],
![(332960103534333644031083407067/790536775148437500000:ℝ), (987489091281469250318001817307/790536775148437500000:ℝ), (30504114145706912592547599184/24704274223388671875:ℝ), (10050083278608924896081398864/24704274223388671875:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (628130204913057806005087429/2947334718357504000000000000:ℝ) row008_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ]
 ring
theorem row008_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
#print axioms row008_identity
#print axioms row008_pos
end
end Record1252270103Finite
