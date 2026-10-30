/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row028_coefficients : Fin 3 → Fin 4 → ℝ := ![![(325897602412115211688594173412063/4144534705753141837500000:ℝ),(959712399158061589441347125227549/4144534705753141837500000:ℝ),(941876503810905787193150607013309/4144534705753141837500000:ℝ),(28005579004017955905932514108893/376775882341194712500000:ℝ)],
![(7596790769528640502409333907745639/51806683821914272968750000:ℝ),(2031793811722050846832272791259743/4709698529264933906250000:ℝ),(2434749636157488345550359183319381/5756298202434919218750000:ℝ),(477319779530565104482342723584193/3453778921460951531250000:ℝ)],
![(7064915361833547225210917408082703/103613367643828545937500000:ℝ),(20763023756379829734637394767589221/103613367643828545937500000:ℝ),(20334994164955511358014042496618383/103613367643828545937500000:ℝ),(1327375290742395826423303777422373/20722673528765709187500000:ℝ)]]
theorem row028_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (1327375290742395826423303777422373/9889245010192626245173248000000000:ℝ) row028_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row028_coefficients,Fin.sum_univ_succ]
 ring
theorem row028_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row028_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row028_pos
