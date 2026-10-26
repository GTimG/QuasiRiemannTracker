/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2690939405335332043933/341003793106687500000:ℝ), (7136321215780810241209/341003793106687500000:ℝ), (6199824215555624350619/341003793106687500000:ℝ), (1754442405110146153343/341003793106687500000:ℝ)],
![(514948236324154758701/85250948276671875000:ℝ), (4527546616557040296701/341003793106687500000:ℝ), (312320437450431517649/34100379310668750000:ℝ), (655450703243893914593/341003793106687500000:ℝ)],
![(732868712388036990871/341003793106687500000:ℝ), (289941567634703698873/85250948276671875000:ℝ), (154078144669509268207/113667931035562500000:ℝ), (0:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (282349746754079299607/4849831724184000000000:ℝ) row002_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
end
end QRH.RepeatedMarks.Return
