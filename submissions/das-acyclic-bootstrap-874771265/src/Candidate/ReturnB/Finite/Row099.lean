/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row099_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29629823846892447682246050707321831/735407006325009995039062500:ℝ),(85178399002288379238796381853997493/735407006325009995039062500:ℝ),(81528511310219267727876667172029493/735407006325009995039062500:ℝ),(8659903147420968097624362008451277/245135668775003331679687500:ℝ)],
![(29129620971183194046377864185847591/367703503162504997519531250:ℝ),(83597427330916510804951060062785077/367703503162504997519531250:ℝ),(79868597381743713271604003214989381/367703503162504997519531250:ℝ),(1693370576109063589174415072536793/24513566877500333167968750:ℝ)],
![(28928312971994527194185881859066351/735407006325009995039062500:ℝ),(2674454896632985431956189166579931/23722806655645483710937500:ℝ),(79095323894690281670880010676987519/735407006325009995039062500:ℝ),(8371765627059485577374694196942003/245135668775003331679687500:ℝ)]]
theorem row099_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (8371765627059485577374694196942003/3743465530566142904374394880000000000:ℝ) row099_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row099_coefficients,Fin.sum_univ_succ]
 ring
theorem row099_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row099_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row099_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row099_pos
