/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(194226895397844061687/39101404749468750000:ℝ), (3579587335774719583487/273709833246281250000:ℝ), (3080409868194713871547/273709833246281250000:ℝ), (286803600068300906623/91236611082093750000:ℝ)],
![(105737520069219155359/34213729155785156250:ℝ), (1992249249596742244363/273709833246281250000:ℝ), (153030714301749751511/27370983324628125000:ℝ), (18283716855928976839/13033801583156250000:ℝ)],
![(581151225753969811063/273709833246281250000:ℝ), (106439562779522662297/34213729155785156250:ℝ), (306961785903836487313/273709833246281250000:ℝ), (0:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (225486868538849039831/15571048291344000000000:ℝ) row005_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(309252101096489627149/109483933298512500000:ℝ), (2854907166395888137609/547419666492562500000:ℝ), (1765797733731198515483/547419666492562500000:ℝ), (18283716855928976839/26067603166312500000:ℝ)],
![(1862662796436634514999/273709833246281250000:ℝ), (183263637233679177857/19550702374734375000:ℝ), (849414162521373974999/273709833246281250000:ℝ), (0:ℝ)],
![(4368743753361070894253/547419666492562500000:ℝ), (7154183852975446117387/547419666492562500000:ℝ), (729431922694731024403/109483933298512500000:ℝ), (189649146162093299627/182473222164187500000:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (67015683103189566043/31142096582688000000000:ℝ) row006_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
end
end QRH.RepeatedMarks.Return
