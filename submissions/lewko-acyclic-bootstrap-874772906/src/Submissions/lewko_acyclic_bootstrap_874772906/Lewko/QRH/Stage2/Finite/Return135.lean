/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def row135_coefficients : Fin 3 → Fin 4 → ℝ := ![![(203944969953442431745821495880846852736/5400727842363000016521919921875:ℝ),(585489756515048647591132474139889492608/5400727842363000016521919921875:ℝ),(559588968749694206328787783587407147008/5400727842363000016521919921875:ℝ),(178042515263484933087531805328364507136/5400727842363000016521919921875:ℝ)],
![(399418318222702669566841494524421257248/5400727842363000016521919921875:ℝ),(228885212207625811638405055101885714848/1080145568472600003304383984375:ℝ),(1091506522468383131311493829206236553216/5400727842363000016521919921875:ℝ),(346495362457520475024622798221229236224/5400727842363000016521919921875:ℝ)],
![(197630464362934227330497565295934951258/5400727842363000016521919921875:ℝ),(565371123448225265247628732764222864218/5400727842363000016521919921875:ℝ),(538316081156978828390255044270779119104/5400727842363000016521919921875:ℝ),(170573670759026703296509161177491206144/5400727842363000016521919921875:ℝ)]]
theorem row135_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (41643962587653003734499306928098439/20135372793008444818931515392000000000:ℝ) row135_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row135_coefficients,Fin.sum_univ_succ]
 ring
theorem row135_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row135_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row135_coefficients]
#print axioms row135_identity
#print axioms row135_pos
end
end LewkoStage2Finite
