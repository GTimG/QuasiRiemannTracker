/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row152_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3674838856967272448859032745966781332913/653539533455748293437500000000000:ℝ),(8664531445571631615603246347505494713187/653539533455748293437500000000000:ℝ),(6352019821715855492868153431799003058111/653539533455748293437500000000000:ℝ),(454048506080593652836007425432734059279/217846511151916097812500000000000:ℝ)],
![(3539001291356243157026716307926449963577/326769766727874146718750000000000:ℝ),(1637306980515533510743161318355103734231/65353953345574829343750000000000:ℝ),(5804744924134008718224987880027447110697/326769766727874146718750000000000:ℝ),(385674938690871095450380035528569884373/108923255575958048906250000000000:ℝ)],
![(3658544488425457434508579047813447260269/653539533455748293437500000000000:ℝ),(8470125801734590471500351020814309341819/653539533455748293437500000000000:ℝ),(601453319335203697780043000202281961313/65353953345574829343750000000000:ℝ),(20046007923189245341457659214351010943/10892325557595804890625000000000:ℝ)]]
theorem row152_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (385674938690871095450380035528569884373/3326732945582858410099998720000000000000000:ℝ) row152_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row152_coefficients,Fin.sum_univ_succ]
 ring
theorem row152_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row152_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row152_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row152_pos
