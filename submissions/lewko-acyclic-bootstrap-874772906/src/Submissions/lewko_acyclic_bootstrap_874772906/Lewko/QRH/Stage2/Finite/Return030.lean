/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row030_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3520109564895909063792763246311751255168/1555343224315706167275779296875:ℝ),(3484737102386243668197272793490333917568/518447741438568722425259765625:ℝ),(10348534728809748720229991697874735099904/1555343224315706167275779296875:ℝ),(1138144152802640774598050521238494867456/518447741438568722425259765625:ℝ)],
![(6785466682973767563889055505431949797024/1555343224315706167275779296875:ℝ),(1343092120970776702448999621480848928608/103689548287713744485051953125:ℝ),(6645750016712099836748993517340505563136/518447741438568722425259765625:ℝ),(6576333835863457403345632485240732557312/1555343224315706167275779296875:ℝ)],
![(3267596123229692706622155945891502005154/1555343224315706167275779296875:ℝ),(3232962923291398294683359067426966509878/518447741438568722425259765625:ℝ),(9595434676597218198654056638792686602752/1555343224315706167275779296875:ℝ),(3164141475076674465022738141778289078272/1555343224315706167275779296875:ℝ)]]
theorem row030_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (772495477313641226812191929145090107/5798739828551345457981751296000000000:ℝ) row030_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row030_coefficients,Fin.sum_univ_succ]
 ring
theorem row030_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row030_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_coefficients]
#print axioms row030_identity
#print axioms row030_pos
end
end LewkoStage2Finite
