/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row194_coefficients : Fin 3 → Fin 4 → ℝ := ![![(242883855543747906987975032/38348595570577095703125:ℝ),(1761865939404804218976853336/115045786711731287109375:ℝ),(1387726174969519156574847464/115045786711731287109375:ℝ),(354511802195958658561919224/115045786711731287109375:ℝ)],
![(78526193850283622078388524/7669719114115419140625:ℝ),(2567987803679041932514290452/115045786711731287109375:ℝ),(1711447559208702204774734704/115045786711731287109375:ℝ),(321352663283914603436272112/115045786711731287109375:ℝ)],
![(772793991276262456690737737/153394382282308382812500:ℝ),(4739120636225664846703915579/460183146846925148437500:ℝ),(138070329822681077888171104/23009157342346257421875:ℝ),(85166983514186020282929928/115045786711731287109375:ℝ)]]
theorem row194_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (10645872939273252535366241/26807611299342299136000000000:ℝ) row194_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row194_coefficients,Fin.sum_univ_succ]
 ring
theorem row194_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row194_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row194_coefficients]
#print axioms row194_identity
#print axioms row194_pos
end
end LewkoStage1Finite
