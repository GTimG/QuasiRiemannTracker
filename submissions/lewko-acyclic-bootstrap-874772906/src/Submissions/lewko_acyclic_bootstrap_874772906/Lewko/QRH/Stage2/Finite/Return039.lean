/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row039_coefficients : Fin 3 → Fin 4 → ℝ := ![![(215902584926989199066834455400327/3333056606486271010546875000:ℝ),(68849233363205200277785181844653/370339622942919001171875000:ℝ),(592213814806171397666356184529973/3333056606486271010546875000:ℝ),(62822600961942736560449667776141/1111018868828757003515625000:ℝ)],
![(178675051984362993312922477965671/1666528303243135505273437500:ℝ),(169613185525259974488813852417287/555509434414378501757812500:ℝ),(160790309356681385624826179357903/555509434414378501757812500:ℝ),(152199552755520246031240708787519/1666528303243135505273437500:ℝ)],
![(29449981584093787442081697880003/666611321297254202109375000:ℝ),(27686098025652341015979416337803/222203773765751400703125000:ℝ),(77926576009467644376460871393059/666611321297254202109375000:ℝ),(24316545835827663598174632759653/666611321297254202109375000:ℝ)]]
theorem row039_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (24316545835827663598174632759653/310663392373595387658240000000000:ℝ) row039_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row039_coefficients,Fin.sum_univ_succ]
 ring
theorem row039_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row039_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_coefficients]
#print axioms row039_identity
#print axioms row039_pos
end
end LewkoStage2Finite
