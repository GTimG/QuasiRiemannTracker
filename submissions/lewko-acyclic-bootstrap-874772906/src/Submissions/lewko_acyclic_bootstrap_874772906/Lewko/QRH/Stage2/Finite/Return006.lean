/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2127801936419094096902682111211/617232704904865001953125:ℝ),(1241905636706452724865689704639/123446540980973000390625:ℝ),(4025164190178914165866137639367/411488469936576667968750:ℝ),(3912025222400903127962301969133/1234465409809730003906250:ℝ)],
![(33958335934036680048921487196018/5555094344143785017578125:ℝ),(98837102010076242773790181659422/5555094344143785017578125:ℝ),(1277843557832059354856564846188/74067924588583800234375:ℝ),(382214224966294885697875157416/68581411656096111328125:ℝ)],
![(2987951528774916982661736519121/1111018868828757003515625:ℝ),(8669633078255455298674189785403/1111018868828757003515625:ℝ),(2793145585969515683485716246731/370339622942919001171875:ℝ),(299748744898235499532796024879/123446540980973000390625:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (299748744898235499532796024879/1840968251102787482419200000000:ℝ) row006_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
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
end LewkoStage2Finite
