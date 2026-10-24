/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row051_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8045923767257875833220638468929472853663/59798792774380330687500000000:ℝ),(13343240725335273473205864027643087904003/33221551541322405937500000000:ℝ),(155586902929761742062276492154441158976/389315057124871944580078125:ℝ),(14073576963387391018070945852883658816/106176833761328712158203125:ℝ)],
![(214505090415426735108149240118290166371/803747214709413046875000000:ℝ),(59547626665626410848880334953707517825527/74748490967975413359375000000:ℝ),(29863390818264250518470780593053627904/37675650689503736572265625:ℝ),(102345383376903003783200617240426382336/389315057124871944580078125:ℝ)],
![(899275658673126588728611422823747922921/6795317360725037578125000000:ℝ),(107369906770079656678926036644173340753/271812694429001503125000000:ℝ),(41729644940519461679478318035797195904/106176833761328712158203125:ℝ),(13839456904865813655524281636881795968/106176833761328712158203125:ℝ)]]
theorem row051_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (108120757069264169183783450288139031/1621425879458615069245440000000000000:ℝ) row051_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row051_coefficients,Fin.sum_univ_succ]
 ring
theorem row051_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row051_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row051_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row051_pos
