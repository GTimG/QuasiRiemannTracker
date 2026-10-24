/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row072_coefficients : Fin 3 → Fin 4 → ℝ := ![![(58673593785165103728751700807/4197340381241009150156250000:ℝ),(126555105266953822337257918079/4197340381241009150156250000:ℝ),(2614607856203928179698492547/125293742723612213437500000:ℝ),(7656428119985271711307313221/1678936152496403660062500000:ℝ)],
![(86572592973394449337068253343/2098670190620504575078125000:ℝ),(170995649180068434767827872671/2098670190620504575078125000:ℝ),(102184381835978760335670323113/2098670190620504575078125000:ℝ),(3325552565429076527732140757/419734038124100915015625000:ℝ)],
![(248786484361336087750384805879/4197340381241009150156250000:ℝ),(51374050215692552950544302783/381576398294637195468750000:ℝ),(421513365227651814779142528439/4197340381241009150156250000:ℝ),(20583634322410207108208000741/839468076248201830031250000:ℝ)]]
theorem row072_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3325552565429076527732140757/382051248923626077312000000000:ℝ) row072_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row072_coefficients,Fin.sum_univ_succ]
 ring
theorem row072_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row072_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row072_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row072_pos
