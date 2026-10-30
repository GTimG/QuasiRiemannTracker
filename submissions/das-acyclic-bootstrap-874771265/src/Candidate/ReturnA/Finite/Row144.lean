/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row144_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1686880740620790107491812350241449809/932526194188619046262500000000000:ℝ),(4078635053184403642961809982100469843/932526194188619046262500000000000:ℝ),(3205819901181684096382503657656379611/932526194188619046262500000000000:ℝ),(812052114937594014987683604347359577/932526194188619046262500000000000:ℝ)],
![(278586258703812704205600194035027541/93252619418861904626250000000000:ℝ),(593836904750484212510011504266161831/93252619418861904626250000000000:ℝ),(378606519263846961034744232308743733/93252619418861904626250000000000:ℝ),(62852504797056316249127316715109443/93252619418861904626250000000000:ℝ)],
![(417299702968593211973318313768495047/186505238837723809252500000000000:ℝ),(940989476867082325724397936952524731/186505238837723809252500000000000:ℝ),(1325372108606323816131340429494273767/373010477675447618505000000000000:ℝ),(276734139759047747426167169719964399/373010477675447618505000000000000:ℝ)]]
theorem row144_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (62852504797056316249127316715109443/86917741030891147115888640000000000000:ℝ) row144_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row144_coefficients,Fin.sum_univ_succ]
 ring
theorem row144_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row144_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row144_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row144_pos
