/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row050_coefficients : Fin 3 → Fin 4 → ℝ := ![![(838844579506958620243587339294817459841/778630114249743889160156250:ℝ),(836759009677380316035147417003912130603/259543371416581296386718750:ℝ),(121162590075188747746116919305773420288/37675650689503736572265625:ℝ),(1248891614074259654501426871216097630976/1167945171374615833740234375:ℝ)],
![(6655261429483603365035438488906462112323/3114520456998975556640625000:ℝ),(19915823258570233645256887632413076173891/3114520456998975556640625000:ℝ),(677247092619466768393892060592477824512/106176833761328712158203125:ℝ),(2477007324916790739660051675436650796544/1167945171374615833740234375:ℝ)],
![(52800598534012617337324412060120227600649/49832327311983608906250000000:ℝ),(158002845035349201756528126723201028773641/49832327311983608906250000000:ℝ),(1231283715533142769092174360640563658496/389315057124871944580078125:ℝ),(37217378491004272898126969986353939712/35392277920442904052734375:ℝ)]]
theorem row050_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (145380384730485441008308476509195077/2161901172611486758993920000000000000:ℝ) row050_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row050_coefficients,Fin.sum_univ_succ]
 ring
theorem row050_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row050_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row050_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row050_pos
