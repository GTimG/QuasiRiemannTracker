/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row060_coefficients : Fin 3 → Fin 4 → ℝ := ![![(693636176668755598513888691115837792611/42713703644558682262500000000:ℝ),(72095213934118160163592368594214498197641/1494979627559553879187500000000:ℝ),(278757456859554592669958364883807522864/5839764170154507340576171875:ℝ),(10218730749379951926913229700561870832/648862685572723037841796875:ℝ)],
![(4299331295817416610253813698281020181/133480323889245882070312500:ℝ),(446834446140062535576717677190592062431/4671811336123605872460937500:ℝ),(110564915194719886830012652251265258496/1167952834030901468115234375:ℝ),(36475443757913484331694046563576169472/1167952834030901468115234375:ℝ)],
![(532955501644717503354760043383939324/33370080972311470517578125:ℝ),(11077388864244125190270537652289775332/233590566806180293623046875:ℝ),(3654409158694977437736056818038956032/77863522268726764541015625:ℝ),(516646606262505202766550443644952576/33370080972311470517578125:ℝ)]]
theorem row060_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (63067212678528467134588677202753/995301433617705884712960000000000:ℝ) row060_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row060_coefficients,Fin.sum_univ_succ]
 ring
theorem row060_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row060_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row060_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row060_pos
