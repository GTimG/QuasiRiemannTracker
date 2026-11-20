/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row017_coefficients : Fin 3 → Fin 4 → ℝ := ![![(930256055529084304180973283235985687/12458081827995902226562500:ℝ),(2776746335282697756084860396136810023/12458081827995902226562500:ℝ),(1105100895501736982960832444074053709/4983232731198360890625000:ℝ),(1832523886687003366116026978006119873/24916163655991804453125000:ℝ)],
![(913494704370575910204471891488164973/6229040913997951113281250:ℝ),(2726533119538676247774986674499628179/6229040913997951113281250:ℝ),(452101657644271184160479966835354994/1038173485666325185546875:ℝ),(149928585806159805062506551385527793/1038173485666325185546875:ℝ)],
![(896876873041885031906707637329322609/12458081827995902226562500:ℝ),(535350100805031672523495615463892127/2491616365599180445312500:ℝ),(242081662861968858386127096998218163/1132552893454172929687500:ℝ),(883024644431834772739856128865261767/12458081827995902226562500:ℝ)]]
theorem row017_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (883024644431834772739856128865261767/6087913702073946713326878720000000000:ℝ) row017_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row017_coefficients,Fin.sum_univ_succ]
 ring
theorem row017_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row017_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row017_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row017_pos
