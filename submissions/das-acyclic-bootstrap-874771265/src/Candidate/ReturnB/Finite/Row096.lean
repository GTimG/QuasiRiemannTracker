/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row096_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2917440316921846059416862998689/839468076248201830031250000:ℝ),(7153638571776399906090316396267/839468076248201830031250000:ℝ),(5705232501875967934565103565217/839468076248201830031250000:ℝ),(1466200340016015607226025167639/839468076248201830031250000:ℝ)],
![(16144381533227077495006769945117/2098670190620504575078125000:ℝ),(38975347181906973799573121609927/2098670190620504575078125000:ℝ),(30401783528859940401903360871003/2098670190620504575078125000:ℝ),(7553814438147653213343259206193/2098670190620504575078125000:ℝ)],
![(22260080217448068352546039338989/4197340381241009150156250000:ℝ),(55344036536691591783970110658919/4197340381241009150156250000:ℝ),(44948004030945633836395498933471/4197340381241009150156250000:ℝ),(11843643581263241344178927613541/4197340381241009150156250000:ℝ)]]
theorem row096_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1466200340016015607226025167639/391220478897793103167488000000000:ℝ) row096_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row096_coefficients,Fin.sum_univ_succ]
 ring
theorem row096_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row096_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row096_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row096_pos
