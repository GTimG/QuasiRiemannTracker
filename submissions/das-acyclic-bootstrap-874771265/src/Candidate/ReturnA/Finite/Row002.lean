/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8283580063944614539152843047/26664220055180730234375000:ℝ),(22303123847293102261693801799/26664220055180730234375000:ℝ),(39879436092217024797160626689/53328440110361460468750000:ℝ),(2366485232951147926540741837/10665688022072292093750000:ℝ)],
![(5057610466833996528570581183/13332110027590365117187500:ℝ),(12803067605366114120245383791/13332110027590365117187500:ℝ),(10695077655387227950741419433/13332110027590365117187500:ℝ),(117667926243632025587664673/533284401103614604687500:ℝ)],
![(2684895911489161885488319319/26664220055180730234375000:ℝ),(6143436819859334191428137333/26664220055180730234375000:ℝ),(4542439112454533939635942759/26664220055180730234375000:ℝ),(213610696511148438989224949/5332844011036146046875000:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (213610696511148438989224949/2427036563244894912000000000:ℝ) row002_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ]
 ring
theorem row002_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row002_pos
