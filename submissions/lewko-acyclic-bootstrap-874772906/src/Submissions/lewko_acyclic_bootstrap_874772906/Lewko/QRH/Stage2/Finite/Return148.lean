/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row148_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1581188983133501694441426588736301/1174100477702695312500000000:ℝ),(159543215063213349979253115239320361/52834521496621289062500000000:ℝ),(3355581346950285425873284154627507/1651078796769415283203125000:ℝ),(593402883756354996829880443809169/1651078796769415283203125000:ℝ)],
![(28857108533594774688058931493339469/11741004777026953125000000000:ℝ),(555968613345333687247628163676779701/105669042993242578125000000000:ℝ),(531176886913622194044382430649823/165107879676941528320312500:ℝ),(68279017315214826770792149029941/165107879676941528320312500:ℝ)],
![(110684156194454506856074157451332713/93928038216215625000000000000:ℝ),(412873353745432320785870493574359229/169070468789188125000000000000:ℝ),(2284165440966656949435267627969341/1651078796769415283203125000:ℝ),(197819028902065070090179638106447/1651078796769415283203125000:ℝ)]]
theorem row148_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (197819028902065070090179638106447/3151701971219408486400000000000000000:ℝ) row148_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newTop,edgeC_newTop,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row148_coefficients,Fin.sum_univ_succ]
 ring
theorem row148_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row148_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row148_coefficients]
#print axioms row148_identity
#print axioms row148_pos
end
end LewkoStage2Finite
