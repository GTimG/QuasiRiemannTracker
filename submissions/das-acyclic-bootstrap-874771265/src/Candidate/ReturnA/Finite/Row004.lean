/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3941624329031632413553646863301/26664220055180730234375000:ℝ),(11307311980489628202401321855951/26664220055180730234375000:ℝ),(10800399628709092260081382410799/26664220055180730234375000:ℝ),(3434648598364981993478707418149/26664220055180730234375000:ℝ)],
![(3225325493129883480656387129573/13332110027590365117187500:ℝ),(9182978959966962779539380230543/13332110027590365117187500:ℝ),(8701585903210306468004756865367/13332110027590365117187500:ℝ),(2743853212765584071928013764397/13332110027590365117187500:ℝ)],
![(517106933880349816914210908089/5332844011036146046875000:ℝ),(1458167340934723825899936068467/5332844011036146046875000:ℝ),(1367488406928684784023668531417/5332844011036146046875000:ℝ),(426408193972400000739505871039/5332844011036146046875000:ℝ)]]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (426408193972400000739505871039/2485285440762772389888000000000:ℝ) row004_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row004_coefficients,Fin.sum_univ_succ]
 ring
theorem row004_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row004_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row004_pos
