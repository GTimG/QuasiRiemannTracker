/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row114_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69487301145013444795814183/1166639489472656250:ℝ),(40485843941450400451954523/233327897894531250:ℝ),(392955286649400521204768137/2333278978945312500:ℝ),(42357149841641135425617091/777759659648437500:ℝ)],
![(67008693241309716389420093/583319744736328125:ℝ),(194826282075046182386147059/583319744736328125:ℝ),(4388587154905929650644448/13565575458984375:ℝ),(20297219609072836326994766/194439914912109375:ℝ)],
![(65181032003133480970328753/1166639489472656250:ℝ),(189168829005123410872816603/1166639489472656250:ℝ),(182879011387050024356702897/1166639489472656250:ℝ),(19630404795020031484738349/388879829824218750:ℝ)]]
theorem row114_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (19630404795020031484738349/5938581870823342080000000000:ℝ) row114_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row114_coefficients,Fin.sum_univ_succ]
 ring
theorem row114_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row114_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row114_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row114_pos
