/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row141_coefficients : Fin 3 → Fin 4 → ℝ := ![![(204338962759700149188630699254620681/59681299762845242460000000000000000:ℝ),(548106368392855005751414192279062043/59681299762845242460000000000000000:ℝ),(483195848506609563936936286794262043/59681299762845242460000000000000000:ℝ),(139428442873454707374152793769820681/59681299762845242460000000000000000:ℝ)],
![(29799184336434582951360789066460681/29840649881422621230000000000000000:ℝ),(75824998710328020280450340710506403/29840649881422621230000000000000000:ℝ),(68317589796441590456161544933296703/29840649881422621230000000000000000:ℝ),(22291775422548153127071993289250981/29840649881422621230000000000000000:ℝ)],
![(93984604964549986554090878878300681/59681299762845242460000000000000000:ℝ),(25018886054546241841720790109389891/11936259952569048492000000000000000:ℝ),(40951861625546670995369814722828093/59681299762845242460000000000000000:ℝ),(1788191676241121873596733654179319/59681299762845242460000000000000000:ℝ)]]
theorem row141_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1788191676241121873596733654179319/3395202830952973793280000000000000000:ℝ) row141_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row141_coefficients,Fin.sum_univ_succ]
 ring
theorem row141_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row141_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row141_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row141_pos
