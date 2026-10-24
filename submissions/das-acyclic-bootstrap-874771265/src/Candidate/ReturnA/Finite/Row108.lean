/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row108_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21833915665592376222195296239/104933511144436563140625000:ℝ),(267176465842832628486695464369/524667555722182815703125000:ℝ),(215643784153808244529716218453/524667555722182815703125000:ℝ),(19117835325875025445915745093/174889185240727605234375000:ℝ)],
![(20828606714661077493829013671/52466755572218281570312500:ℝ),(45992376905103704641963712093/52466755572218281570312500:ℝ),(32029909510029762009175605463/52466755572218281570312500:ℝ),(2260374040397802872055302347/17488918524072760523437500:ℝ)],
![(37584039571584887517393510403/104933511144436563140625000:ℝ),(439997018182526116342195683961/524667555722182815703125000:ℝ),(167199504340649139261846948151/262333777861091407851562500:ℝ),(6807046614061971077658605363/43722296310181901308593750:ℝ)]]
theorem row108_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2260374040397802872055302347/509401673063836637184000000000:ℝ) row108_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row108_coefficients,Fin.sum_univ_succ]
 ring
theorem row108_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row108_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row108_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row108_pos
