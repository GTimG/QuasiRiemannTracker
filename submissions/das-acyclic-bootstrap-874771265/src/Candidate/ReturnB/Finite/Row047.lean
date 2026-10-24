/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row047_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1336639995522980161107153237106712030789/1195975855487606613750000000000:ℝ),(794365573417993601083337033337779298019/239195171097521322750000000000:ℝ),(1311298029795242975587496744461594550797/398658618495868871250000000000:ℝ),(28860132529208598155252926306724426513/26577241233057924750000000000:ℝ)],
![(1294537823118713402365887785700601788757/597987927743803306875000000000:ℝ),(769158567972323862318828626850617267843/119597585548760661375000000000:ℝ),(141041941185313283273687913747925522849/22147701027548270625000000000:ℝ),(27930602990486076979493338058700101477/13288620616528962375000000000:ℝ)],
![(139263396776894365158026865815002562069/132886206165289623750000000000:ℝ),(49634098299343986322978305980137524413/15946344739834754850000000000:ℝ),(1228388360551974182144484786262776343103/398658618495868871250000000000:ℝ),(27021733614405892923829049946956394599/26577241233057924750000000000:ℝ)]]
theorem row047_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (27021733614405892923829049946956394599/405860913471596447555125248000000000000:ℝ) row047_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row047_coefficients,Fin.sum_univ_succ]
 ring
theorem row047_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row047_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row047_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row047_pos
