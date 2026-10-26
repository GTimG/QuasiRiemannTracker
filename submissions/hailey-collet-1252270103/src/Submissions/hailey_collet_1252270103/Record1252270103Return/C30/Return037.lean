/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.C30.ReturnFormulas
set_option autoImplicit false
namespace Record1252270103Return.C30
noncomputable section
def row037_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3419745847553359097522557/26664878889575648437500:ℝ), (6083349083164262945343121/17776585926383765625000:ℝ), (16165265891946998925596959/53329757779151296875000:ℝ), (158307082874246694903757/1777658592638376562500:ℝ)],
![(2191403600795920819146523/13332439444787824218750:ℝ), (3606100408522059930746989/8888292963191882812500:ℝ), (731513796988695924431933/2222073240797970703125:ℝ), (93267033488918322569411/1066595155583025937500:ℝ)],
![(1816337478504903290770489/26664878889575648437500:ℝ), (1384144002934630045779941/8888292963191882812500:ℝ), (3068528060544951572181829/26664878889575648437500:ℝ), (144287565515781970122499/5332975777915129687500:ℝ)]]
theorem row037_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (144287565515781970122499/2427096531815596800000000:ℝ) row037_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row037_coefficients,Fin.sum_univ_succ]
 ring
theorem row037_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row037_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_coefficients]
#print axioms row037_identity
#print axioms row037_pos
end
end Record1252270103Return.C30
