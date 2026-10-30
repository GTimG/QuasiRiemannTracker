/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row013_coefficients : Fin 3 → Fin 4 → ℝ := ![![(421023834764482290068282010778536169/5536925256887067656250000:ℝ),(11310989674534976121518947694645963027/49832327311983608906250000:ℝ),(3751482019558691315369289684620959697/16610775770661202968750000:ℝ),(746534167201738182650139337244748317/9966465462396721781250000:ℝ)],
![(82702111753934154933190755103547317/553692525688706765625000:ℝ),(11108414410636875595669992310269178451/24916163655991804453125000:ℝ),(11052154333102229777456185516605765307/24916163655991804453125000:ℝ),(3665334889576844322327635958496216121/24916163655991804453125000:ℝ)],
![(12304880889875432310059186574640897/167785613845062656250000:ℝ),(39663860173311962045201808813528913/181208462952667668750000:ℝ),(986507741958851669790852752719431643/4530211573816691718750000:ℝ),(109047671986384027624113310173837679/1510070524605563906250000:ℝ)]]
theorem row013_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (109047671986384027624113310173837679/737928933584720813736591360000000000:ℝ) row013_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row013_coefficients,Fin.sum_univ_succ]
 ring
theorem row013_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row013_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row013_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row013_pos
