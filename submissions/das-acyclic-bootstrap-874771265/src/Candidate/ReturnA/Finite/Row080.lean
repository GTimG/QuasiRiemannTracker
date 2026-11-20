/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row080_coefficients : Fin 3 → Fin 4 → ℝ := ![![(133192368370589501748853079/2333278978945312500:ℝ),(387836167037138202872344919/2333278978945312500:ℝ),(94064360913245270359673344/583319744736328125:ℝ),(30403411246608095078800384/583319744736328125:ℝ)],
![(63952118250051556716985201/583319744736328125:ℝ),(185822083570855222116197233/583319744736328125:ℝ),(179870575626347533455116288/583319744736328125:ℝ),(58000610305543868055904256/583319744736328125:ℝ)],
![(1239033476157862843804319/23332789789453125:ℝ),(89824826595904842788295047/583319744736328125:ℝ),(86764367173071795052294144/583319744736328125:ℝ),(27915377481113523359107072/583319744736328125:ℝ)]]
theorem row080_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (13630555410699962577689/4349547268669440000000000:ℝ) row080_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row080_coefficients,Fin.sum_univ_succ]
 ring
theorem row080_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row080_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row080_pos
