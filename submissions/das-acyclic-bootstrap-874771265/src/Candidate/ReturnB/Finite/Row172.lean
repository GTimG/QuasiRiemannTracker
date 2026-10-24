/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row172_coefficients : Fin 3 → Fin 4 → ℝ := ![![(103996371318193114974162178429443121790945585837/27230813893989512226562500000000:ℝ),(1258221528377437946984201580230367411464694109/164702503391065598144531250000:ℝ),(1219686803760962887072366730748977523747713024/319111100320189596405029296875:ℝ),(590062756631059062567321055539487137857536/319111100320189596405029296875:ℝ)],
![(26004177959266164100884037106448706457799808289/3403851736748689028320312500000:ℝ),(9753498548355514784432647313184567847855460239/638222200640379192810058593750:ℝ),(2440225156935147062798784850398978920469594112/319111100320189596405029296875:ℝ),(1367554121119540401303566814758228864270336/319111100320189596405029296875:ℝ)],
![(6503661592177165874420605590513284278748756069/1701925868374344514160156250000:ℝ),(487940410236285491087671085254546524881863631/63822220064037919281005859375:ℝ),(244259061186937229990967121666952585432203264/63822220064037919281005859375:ℝ),(1029797127125591716721240497850666652270592/319111100320189596405029296875:ℝ)]]
theorem row172_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (281363848033456355365429427880996293/319366362775954407369599877120000000000000000:ℝ) row172_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row172_coefficients,Fin.sum_univ_succ]
 ring
theorem row172_pos {δ p : ℝ} (hd : δ∈Set.Icc (30033/65536:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row172_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row172_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row172_pos
