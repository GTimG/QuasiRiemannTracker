/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row182_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33613208762765352803883536614572806797/84930165491931028733765625000000:ℝ),(77259251132175454021947918545892325711/84930165491931028733765625000000:ℝ),(54548543116156369903432477753415347997/84930165491931028733765625000000:ℝ),(10896208641494779479353025755064579083/84930165491931028733765625000000:ℝ)],
![(38142032697350430824515499158705969243/42465082745965514366882812500000:ℝ),(447256911168196067263865585650148111783/212325413729827571834414062500000:ℝ),(653880700009622028159884680241478361649/424650827459655143668828125000000:ℝ),(140721137541593565214150264824413705513/424650827459655143668828125000000:ℝ)],
![(470295315764018954058487952223195522673/849301654919310287337656250000000:ℝ),(1432098792956016004450649114884360043267/1061627068649137859172070312500000:ℝ),(3560094069433543680077994585473007877811/3397206619677241149350625000000000:ℝ),(4291408565943888040423023183898798525243/16986033098386205746753125000000000:ℝ)]]
theorem row182_identity (δ p : ℝ) : rowMargin .newTop .P δ p =
 Record12518109.Bernstein.bsum 2 3 (10896208641494779479353025755064579083/40530253692412391144351072256000000000000:ℝ) row182_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row182_coefficients,Fin.sum_univ_succ]
 ring
theorem row182_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .P δ p := by
 rw [row182_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row182_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row182_pos
