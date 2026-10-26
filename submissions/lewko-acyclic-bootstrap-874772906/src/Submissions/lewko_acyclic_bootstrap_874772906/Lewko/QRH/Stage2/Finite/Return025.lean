/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row025_coefficients : Fin 3 → Fin 4 → ℝ := ![![(55340673964108598611824652201027970206466/1555343224315706167275779296875:ℝ),(10954351918405617913643776198433305408222/103689548287713744485051953125:ℝ),(6022798853563314446024260155520769928704/57605304604285413602806640625:ℝ),(53640955889307462672977057432964177158144/1555343224315706167275779296875:ℝ)],
![(109657860130641326555811693079747122633088/1555343224315706167275779296875:ℝ),(108522985942734246938568304559001249745024/518447741438568722425259765625:ℝ),(64435684350388970709436780290783590416384/311068644863141233455155859375:ℝ),(35422435753187699199346972618887108493312/518447741438568722425259765625:ℝ)],
![(10863885034336912430102580913098091177984/311068644863141233455155859375:ℝ),(10750693154305983164197011464069555697664/103689548287713744485051953125:ℝ),(31913914412201206182633189007900613804032/311068644863141233455155859375:ℝ),(10525718293575354862107023528790037889024/311068644863141233455155859375:ℝ)]]
theorem row025_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2509526799577559199835544473836431/18121061964222954556192972800000000:ℝ) row025_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row025_coefficients,Fin.sum_univ_succ]
 ring
theorem row025_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row025_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_coefficients]
#print axioms row025_identity
#print axioms row025_pos
end
end LewkoStage2Finite
