/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(420614217439674164802479/53281814226166687500000:ℝ), (371825046580587680316589/17760604742055562500000:ℝ), (107678625240500398610233/5920201580685187500000:ℝ), (274246704862414711344809/53281814226166687500000:ℝ)],
![(10061628859262253732911/1665056694567708984375:ℝ), (235906196568130448706071/17760604742055562500000:ℝ), (48821257887184030174597/5328181422616668750000:ℝ), (102466112663841075080909/53281814226166687500000:ℝ)],
![(114485162961384704650673/53281814226166687500000:ℝ), (30193492373937014100041/8880302371027781250000:ℝ), (72198253876515129949573/53281814226166687500000:ℝ), (0:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (44088694112253455943541/757785802327704000000000:ℝ) row002_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
end
end QRH.RepeatedMarks.Return
