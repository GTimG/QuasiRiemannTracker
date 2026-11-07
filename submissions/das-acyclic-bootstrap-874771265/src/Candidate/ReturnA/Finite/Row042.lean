/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row042_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10016202821391006947787047761163/189727955437500000000000:ℝ),(29749767857569419070504559181697/189727955437500000000000:ℝ),(29452168752843635945374223505353/189727955437500000000000:ℝ),(3239534572221741274218904028273/63242651812500000000000:ℝ)],
![(9445750017640684613750881706843/94863977718750000000000:ℝ),(28038324506285884052849197911073/94863977718750000000000:ℝ),(27740690889866173985456449303981/94863977718750000000000:ℝ),(9148116401220974546358133099751/94863977718750000000000:ℝ)],
![(8899160369696902075877203608083/189727955437500000000000:ℝ),(26398490267447577393786157322641/189727955437500000000000:ℝ),(580018745682497067953561742143/4216176787500000000000:ℝ),(8601513657961692740001324681877/189727955437500000000000:ℝ)]]
theorem row042_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (8601513657961692740001324681877/90541707082334208000000000000000:ℝ) row042_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row042_coefficients,Fin.sum_univ_succ]
 ring
theorem row042_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row042_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row042_pos
