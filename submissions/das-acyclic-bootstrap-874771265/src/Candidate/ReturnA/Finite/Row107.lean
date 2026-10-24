/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row107_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7334192268823152359913166021/524667555722182815703125000:ℝ),(15819370126162170317348691037/524667555722182815703125000:ℝ),(21897309746685556056604451347/1049335111444365631406250000:ℝ),(2386662693940802859655063/523359157827613781250000:ℝ)],
![(10821572210403128541389380429/262333777861091407851562500:ℝ),(21374452689750057633456312013/262333777861091407851562500:ℝ),(12773046113512763514381668939/262333777861091407851562500:ℝ),(415694060701924802837947471/52466755572218281570312500:ℝ)],
![(31098313935092954825365594837/524667555722182815703125000:ℝ),(70639329666814809005341822639/524667555722182815703125000:ℝ),(52689181279287311127758238917/524667555722182815703125000:ℝ),(2572954977250607226306402223/104933511144436563140625000:ℝ)]]
theorem row107_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (415694060701924802837947471/47756406849734684736000000000:ℝ) row107_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row107_coefficients,Fin.sum_univ_succ]
 ring
theorem row107_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row107_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row107_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row107_pos
