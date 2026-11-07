/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row213_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5413336330716879632722163035221314716678/2417012448450378685524052734375:ℝ),(13882234435096138385167722478967138392282/2417012448450378685524052734375:ℝ),(2309688227492518560841975683991540407296/483402489690075737104810546875:ℝ),(3079496304339213537456779655053011173376/2417012448450378685524052734375:ℝ)],
![(3626613535763550309659767244357264191576/805670816150126228508017578125:ℝ),(27906545546712003112888559115794339878264/2417012448450378685524052734375:ℝ),(23221677592082788650896373500539029458944/2417012448450378685524052734375:ℝ),(2064959633451540181845763197782108635136/805670816150126228508017578125:ℝ)],
![(218955099054754707258256716107440390424/96680497938015147420962109375:ℝ),(1560707191553758733022935971071826031848/268556938716708742836005859375:ℝ),(3898408100422484443480243472408968613888/805670816150126228508017578125:ℝ),(3122690029624783482480874683134762565632/2417012448450378685524052734375:ℝ)]]
theorem row213_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (187957538106641451260789773867981639/1153443268902140259237919457280000000000:ℝ) row213_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row213_coefficients,Fin.sum_univ_succ]
 ring
theorem row213_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row213_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row213_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row213_pos
