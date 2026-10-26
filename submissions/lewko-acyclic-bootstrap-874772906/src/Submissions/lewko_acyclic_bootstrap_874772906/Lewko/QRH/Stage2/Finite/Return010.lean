/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row010_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3922359032742015499254471657663223908658/1555343224315706167275779296875:ℝ),(3884773769882906564628531907672188897382/518447741438568722425259765625:ℝ),(11541990388628793017321934909876990781952/1555343224315706167275779296875:ℝ),(423336406648128126148509630988738666496/172815913812856240808419921875:ℝ)],
![(7576531597574625555089555832507074324216/1555343224315706167275779296875:ℝ),(7502097424725907601403135689689619896232/518447741438568722425259765625:ℝ),(7427948422538842871317486756050199324672/518447741438568722425259765625:ℝ),(7354083662809131034050959394088812609536/1555343224315706167275779296875:ℝ)],
![(3656411573383554002164424424115153878856/1555343224315706167275779296875:ℝ),(3619563079066422602832729723030486783256/518447741438568722425259765625:ℝ),(10748574244458222414963593142919512205312/1555343224315706167275779296875:ℝ),(141851844159882283496705197417728229376/62213728972628246691031171875:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .oldSmall .weakC7 δ p =
 Record12518109.Bernstein.bsum 2 3 (8657949472649065154828198084578139/57987398285513454579817512960000000:ℝ) row010_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row010_coefficients,Fin.sum_univ_succ]
 ring
theorem row010_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .weakC7 δ p := by
 rw [row010_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]
#print axioms row010_identity
#print axioms row010_pos
end
end LewkoStage2Finite
