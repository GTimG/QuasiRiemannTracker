/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row021_coefficients : Fin 3 → Fin 4 → ℝ := ![![(38340795111718433388664712121532877/4152693942665300742187500:ℝ),(68319425446068343444464240085333819/2491616365599180445312500:ℝ),(84535262433428860078235600981066368/3114520456998975556640625:ℝ),(27891572942994921114960960434298752/3114520456998975556640625:ℝ)],
![(75296770946045960252515736396495557/4152693942665300742187500:ℝ),(21637623232272343567393912673625361/401873607354706523437500:ℝ),(2049042244137225136866013828326656/38450869839493525390625:ℝ),(54753411798273673340122455889984256/3114520456998975556640625:ℝ)],
![(29569564661789272013705390672936089/3322155154132240593750000:ℝ),(1316892092366181083101819787896415159/49832327311983608906250000:ℝ),(81450619110012026424212432097891968/3114520456998975556640625:ℝ),(8955442029088306284568861200810368/1038173485666325185546875:ℝ)]]
theorem row021_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (69964390852252392848194228131331/495435685390132382269440000000000:ℝ) row021_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row021_coefficients,Fin.sum_univ_succ]
 ring
theorem row021_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row021_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row021_pos
