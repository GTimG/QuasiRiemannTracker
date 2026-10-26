/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section
def row019_coefficients : Fin 3 → Fin 4 → ℝ := ![![(184944506970581294360840633415217143992/632205024847982657208984375:ℝ), (552021611581453956383307732379496822456/632205024847982657208984375:ℝ), (183071760800236087232393055419331469312/210735008282660885736328125:ℝ), (6745858319181582808946821358100545536/23415000920295653970703125:ℝ)],
![(366499553383878662220987716430846055616/632205024847982657208984375:ℝ), (364629705494655518437329665427084733504/210735008282660885736328125:ℝ), (1088290749999025066033065547330616754176/632205024847982657208984375:ℝ), (72180236102828655858164928496041721856/126441004969596531441796875:ℝ)],
![(60520786553817249588564658709720148608/210735008282660885736328125:ℝ), (541889446938760526612062330328410742656/632205024847982657208984375:ℝ), (107819482360602386850813206767113207808/126441004969596531441796875:ℝ), (178770321312710100247719029636315742208/632205024847982657208984375:ℝ)]]
theorem row019_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (170488663971624469993323354374233/1178515584239996911583232000000000:ℝ) row019_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row019_coefficients,Fin.sum_univ_succ]
 ring
theorem row019_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row019_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row019_coefficients]
#print axioms row019_identity
#print axioms row019_pos
end
end LewkoStage2Return.C30
