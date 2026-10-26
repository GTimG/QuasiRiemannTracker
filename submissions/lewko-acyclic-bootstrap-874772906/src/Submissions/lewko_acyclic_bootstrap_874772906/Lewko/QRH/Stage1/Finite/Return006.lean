/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2298026244758516115256641477827/666611335526913052734375:ℝ),(6706290889775248867984593254803/666611335526913052734375:ℝ),(2608306572364594124319467927177/266644534210765221093750:ℝ),(1408329176522869929578608902311/444407557017942035156250:ℝ)],
![(4075000602170057952721583025202/666611335526913052734375:ℝ),(11860453094142899955142748406878/666611335526913052734375:ℝ),(460023714242144680978765212004/26664453421076522109375:ℝ),(1238374179796963774976873722808/222203778508971017578125:ℝ)],
![(358554210818181338146048791409/133322267105382610546875:ℝ),(1040356049763722346464075609627/133322267105382610546875:ℝ),(1005532489594791037629297823777/133322267105382610546875:ℝ),(107909556709383946914225751853/44440755701794203515625:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (107909556709383946914225751853/662748584544207057715200000000:ℝ) row006_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ]
 ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
#print axioms row006_identity
#print axioms row006_pos
end
end LewkoStage1Finite
