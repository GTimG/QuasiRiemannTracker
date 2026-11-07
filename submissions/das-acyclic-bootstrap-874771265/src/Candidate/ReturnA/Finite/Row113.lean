/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row113_coefficients : Fin 3 → Fin 4 → ℝ := ![![(528643387241816080640366/64813304970703125:ℝ),(315354804768015066854426/13565575458984375:ℝ),(12866542429274541361808704/583319744736328125:ℝ),(812815261885247642566336/116663948947265625:ℝ)],
![(112646253320203317081043/7201478330078125:ℝ),(25906870155645796619886787/583319744736328125:ℝ),(979212598282719620150912/23332789789453125:ℝ),(7697791320358662567450496/583319744736328125:ℝ)],
![(3917506714498208368034543/518506439765625000:ℝ),(99740888745774087996762727/4666557957890625000:ℝ),(11733858162439291737925696/583319744736328125:ℝ),(3673442123028015152369216/583319744736328125:ℝ)]]
theorem row113_identity (δ p : ℝ) : rowMargin .newSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (57397533172312736755769/17398189074677760000000000:ℝ) row113_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row113_coefficients,Fin.sum_univ_succ]
 ring
theorem row113_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capC δ p := by
 rw [row113_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row113_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row113_pos
