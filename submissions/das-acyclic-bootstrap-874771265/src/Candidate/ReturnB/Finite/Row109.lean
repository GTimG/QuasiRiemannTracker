/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row109_coefficients : Fin 3 → Fin 4 → ℝ := ![![(161427667920104671494627862163/41973403812410091501562500:ℝ),(10712409587923264368325913049137/1049335095310252287539062500:ℝ),(9444934765031648421475956701449/1049335095310252287539062500:ℝ),(2765949749506682055983240206387/1049335095310252287539062500:ℝ)],
![(3285357001256292671942106681443/524667547655126143769531250:ℝ),(1644762882147919401357487120237/104933509531025228753906250:ℝ),(6746190149250275427391843708291/524667547655126143769531250:ℝ),(1804898832761572611880889788549/524667547655126143769531250:ℝ)],
![(3674651988410754471422720419361/1049335095310252287539062500:ℝ),(9025602991495840574067820508333/1049335095310252287539062500:ℝ),(14430190808240601219322608939041/2098670190620504575078125000:ℝ),(3721204034556932812368346261097/2098670190620504575078125000:ℝ)]]
theorem row109_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1804898832761572611880889788549/489025598622241378959360000000000:ℝ) row109_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row109_coefficients,Fin.sum_univ_succ]
 ring
theorem row109_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row109_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row109_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row109_pos
