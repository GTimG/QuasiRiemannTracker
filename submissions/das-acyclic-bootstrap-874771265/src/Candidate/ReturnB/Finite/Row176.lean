/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row176_coefficients : Fin 3 → Fin 4 → ℝ := ![![(59129527065970863425452551788808597931457/163384883363937073359375000000000:ℝ),(137709275933531571038929082037468888166091/163384883363937073359375000000000:ℝ),(98434528494233651288965161672716469424729/163384883363937073359375000000000:ℝ),(3970798850195822307218094504440406463019/32676976672787414671875000000000:ℝ)],
![(60498837786472431323715913822962780071861/81692441681968536679687500000000:ℝ),(141517894765316763474375227355647360888483/81692441681968536679687500000000:ℝ),(50973153433334189048633488469778753099101/40846220840984268339843750000000:ℝ),(261580744267474679541115787412271586801/1021155521024606708496093750000:ℝ)],
![(62369861229949817434565679089092649268623/163384883363937073359375000000000:ℝ),(146827157683693262832241579543949496914639/163384883363937073359375000000000:ℝ),(213908500679731392455414366186636057217797/326769766727874146718750000000000:ℝ),(8998463415001443669360296179919407697653/65353953345574829343750000000000:ℝ)]]
theorem row176_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3970798850195822307218094504440406463019/63873272555190881473919975424000000000000000:ℝ) row176_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row176_coefficients,Fin.sum_univ_succ]
 ring
theorem row176_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row176_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row176_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row176_pos
