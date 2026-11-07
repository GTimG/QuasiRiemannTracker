/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row143_coefficients : Fin 3 → Fin 4 → ℝ := ![![(927845289479967812148328364594036323/7460162470355655307500000000000000:ℝ),(2062072251415681171935551950789138073/7460162470355655307500000000000000:ℝ),(1461880732415554352505207880123829629/7460162470355655307500000000000000:ℝ),(107875616053092943161451429742909293/2486720823451885102500000000000000:ℝ)],
![(1059016370026601095781561784199521883/3730081235177827653750000000000000:ℝ),(424976664039803121975538164243589621/746016247035565530750000000000000:ℝ),(1248560531969281801279986667617158299/3730081235177827653750000000000000:ℝ),(58884399438674680777804207849577359/1243360411725942551250000000000000:ℝ)],
![(221328096828492554606136474336909173/678196588214150482500000000000000:ℝ),(5640801924229900481118788819740734593/7460162470355655307500000000000000:ℝ),(2116221718759246757707497353482854587/3730081235177827653750000000000000:ℝ),(7705984872581411118848784805727087/56516382351179206875000000000000:ℝ)]]
theorem row143_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (58884399438674680777804207849577359/36215496863498387128320000000000000000:ℝ) row143_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row143_coefficients,Fin.sum_univ_succ]
 ring
theorem row143_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row143_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row143_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row143_pos
