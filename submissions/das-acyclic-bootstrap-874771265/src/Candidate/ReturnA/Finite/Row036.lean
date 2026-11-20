/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row036_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8451922301599942683265927169/284418347255261122500000000:ℝ),(66685980816558096417649924681/853255041765783367500000000:ℝ),(57304660918716708685906504841/853255041765783367500000000:ℝ),(15974447006958440318054361667/853255041765783367500000000:ℝ)],
![(5678012441318411114064331193/142209173627630561250000000:ℝ),(42279694093389344989345383433/426627520882891683750000000:ℝ),(3786139677604712819928122681/47403057875876853750000000:ℝ),(353184013160332149288028571/17065100835315667350000000:ℝ)],
![(4041775970057924034862735217/284418347255261122500000000:ℝ),(5461013561895238166563865327/170651008353156673500000000:ℝ),(19702855137535588594893858517/853255041765783367500000000:ℝ),(1478387869636821452220912511/284418347255261122500000000:ℝ)]]
theorem row036_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1478387869636821452220912511/16180243754965966080000000000:ℝ) row036_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row036_coefficients,Fin.sum_univ_succ]
 ring
theorem row036_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row036_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row036_pos
