/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8959051096056161069/1137392487562500000:ℝ), (71272233283394530511/3412177462687500000:ℝ), (61913006702283611401/3412177462687500000:ℝ), (17517926707057564097/3412177462687500000:ℝ)],
![(428440021511261917/71087030472656250:ℝ), (45214057997999180629/3412177462687500000:ℝ), (38513778882431741/4212564768750000:ℝ), (6547223929311101597/3412177462687500000:ℝ)],
![(2445559198374029603/1137392487562500000:ℝ), (5810199287310350059/1706088731343750000:ℝ), (356577386865277793/262475189437500000:ℝ), (0:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (947297054939277151/16176248712000000000:ℝ) row002_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
end
end QRH.RepeatedMarks.Return
