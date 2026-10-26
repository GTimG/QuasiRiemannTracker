/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row200_coefficients : Fin 3 → Fin 4 → ℝ := ![![(879521056987263865539677213547681826/2021064041969660670323572265625:ℝ),(2095605065160427072138590850764890554/2021064041969660670323572265625:ℝ),(1571502506247523561191656511628856213/2021064041969660670323572265625:ℝ),(71064025236246623087372661605766997/404212808393932134064714453125:ℝ)],
![(1771825329089080296916052784157729196/2021064041969660670323572265625:ℝ),(4164768199449106150551257789476152932/2021064041969660670323572265625:ℝ),(3053542877809919646000693397201035916/2021064041969660670323572265625:ℝ),(132078581745504131460095755689022436/404212808393932134064714453125:ℝ)],
![(201344318578355896655149306735749326/404212808393932134064714453125:ℝ),(481774810627914556799815766174351018/404212808393932134064714453125:ℝ),(363650249117778556117399769802108058/404212808393932134064714453125:ℝ),(83197957202706934386942824738506366/404212808393932134064714453125:ℝ)]]
theorem row200_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (33019645436376032865023938922255609/96448932926458488925079784652800000000:ℝ) row200_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row200_coefficients,Fin.sum_univ_succ]
 ring
theorem row200_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row200_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row200_coefficients]
#print axioms row200_identity
#print axioms row200_pos
end
end LewkoStage2Finite
