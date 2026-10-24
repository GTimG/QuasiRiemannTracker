/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row103_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29306232075667524484467512082697/131166888930545703925781250:ℝ),(15021569201574014298735074862893/26233377786109140785156250:ℝ),(31522973771238126692130607404832/65583444465272851962890625:ℝ),(8618261327585641388152730976448/65583444465272851962890625:ℝ)],
![(29915572420975862261430631811086/65583444465272851962890625:ℝ),(76337314130684363672413833580894/65583444465272851962890625:ℝ),(296317074910387701676124618752/305039276582664427734375:ℝ),(17278246490679458298314372511872/65583444465272851962890625:ℝ)],
![(629685834677764006612626340322/2623337778610914078515625:ℝ),(40194422692345859527023184740674/65583444465272851962890625:ℝ),(33568833736612801725324303830848/65583444465272851962890625:ℝ),(9112270627458691998770996348224/65583444465272851962890625:ℝ)]]
theorem row103_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (134660333243525646689886421507/61128200767660396462080000000000:ℝ) row103_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row103_coefficients,Fin.sum_univ_succ]
 ring
theorem row103_pos {δ p : ℝ} (hd : δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row103_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row103_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row103_pos
