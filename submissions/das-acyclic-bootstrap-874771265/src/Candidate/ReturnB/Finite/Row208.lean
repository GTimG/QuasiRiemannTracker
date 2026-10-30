/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row208_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1350205077187909652324195207835224232166/2417012448450378685524052734375:ℝ),(3490860783177029207938497651209271724538/2417012448450378685524052734375:ℝ),(2936849207573705362623848120993412451328/2417012448450378685524052734375:ℝ),(796182329634646058815826641796122771456/2417012448450378685524052734375:ℝ)],
![(2675381728738590440020923813136306717168/2417012448450378685524052734375:ℝ),(6898384618038174500754442661613945391376/2417012448450378685524052734375:ℝ),(5782181147195409860206357215779588661248/2417012448450378685524052734375:ℝ),(311831153968350706428193042264452497408/483402489690075737104810546875:ℝ)],
![(444183283781925724298669270045538129184/805670816150126228508017578125:ℝ),(381064160803234351366836901469322940832/268556938716708742836005859375:ℝ),(191154652417930798755782962095450308608/161134163230025245701603515625:ℝ),(9509640417487456144759300177377624064/29839659857412082537333984375:ℝ)]]
theorem row208_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (326487593678997441493353659043879/2002505675177326838954721280000000000:ℝ) row208_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row208_coefficients,Fin.sum_univ_succ]
 ring
theorem row208_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row208_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row208_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row208_pos
