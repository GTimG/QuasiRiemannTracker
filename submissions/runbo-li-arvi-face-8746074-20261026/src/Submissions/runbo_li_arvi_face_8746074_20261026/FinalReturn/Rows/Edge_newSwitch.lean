/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(114536443256624512151309/22619831596511906250000:ℝ), (18996538718230565472699181/1425049390580250093750000:ℝ), (16345689660959098148800961/1425049390580250093750000:ℝ), (15580023439917668742779/4863649797202218750000:ℝ)],
![(21219536373397997822021/6597450882315972656250:ℝ), (10783422589507526030192969/1425049390580250093750000:ℝ), (275557375442778035417911/47501646352675003125000:ℝ), (295245504347111794557271/203578484368607156250000:ℝ)],
![(340869054867513737669341/158338821175583343750000:ℝ), (281653625078739020717668/89065586911265630859375:ℝ), (1629882719438950567458619/1425049390580250093750000:ℝ), (0:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (133377483290086564206317/9007719604655408000000000:ℝ) row005_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1640472303609005967989807/570019756232100037500000:ℝ), (15213071593808996348668067/2850098781160500187500000:ℝ), (9459921030167248820619929/2850098781160500187500000:ℝ), (295245504347111794557271/407156968737214312500000:ℝ)],
![(9754584649006309588440637/1425049390580250093750000:ℝ), (960183214772937070102891/101789242184303578125000:ℝ), (4452965205761808892999837/1425049390580250093750000:ℝ), (0:ℝ)],
![(22707202904609590086932239/2850098781160500187500000:ℝ), (2854708206138382243245437/219238367781576937500000:ℝ), (1257580774372385618188283/190006585410700012500000:ℝ), (2929738144502406197565803/2850098781160500187500000:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (334076168791775593812809/162138952883797344000000000:ℝ) row006_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
end
end QRH.RepeatedMarks.Return
