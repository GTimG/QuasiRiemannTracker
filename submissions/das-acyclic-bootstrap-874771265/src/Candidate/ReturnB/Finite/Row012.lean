/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row012_coefficients : Fin 3 → Fin 4 → ℝ := ![![(246358366424138728052683560966815353/99664654623967217812500000:ℝ),(81326461179607491109058802839768563/11073850513774135312500000:ℝ),(28993154221657032898501956484529819/3986586184958688712500000:ℝ),(79749680280907789852440620840714587/33221551541322405937500000:ℝ)],
![(79278436641181822937549483869882691/16610775770661202968750000:ℝ),(28257577013371853763336015497909987/1993293092479344356250000:ℝ),(699400752068484360476214376191845831/49832327311983608906250000:ℝ),(76932201782853471576567532617914743/16610775770661202968750000:ℝ)],
![(229455681924557832458250708688022993/99664654623967217812500000:ℝ),(681371086710137472577671071320922683/99664654623967217812500000:ℝ),(674403126602893293293783829657222737/99664654623967217812500000:ℝ),(74162563228071658526940156924774349/33221551541322405937500000:ℝ)]]
theorem row012_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (74162563228071658526940156924774349/507326141839495559443906560000000000:ℝ) row012_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row012_coefficients,Fin.sum_univ_succ]
 ring
theorem row012_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row012_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row012_pos
