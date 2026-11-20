/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row158_coefficients : Fin 3 → Fin 4 → ℝ := ![![(321605839867363673876562715967808117195853/1361558184284276992567968750000000:ℝ),(79188614372428895648680439105184825350231/163386982114113239108156250000000:ℝ),(8394904189026337136854881275542203734792/31911519944162742013311767578125:ℝ),(93173818032377725279484841139830711344/6382303988832548402662353515625:ℝ)],
![(25117483285518971359083473667699308127059/54462327371371079702718750000000:ℝ),(761626558584514705052764762760878299263717/816934910570566195540781250000000:ℝ),(17715097305593412671791576126103887352/36470308507614562300927734375:ℝ),(13332991870473947337321050618679243808/911757712690364057523193359375:ℝ)],
![(9935197457026397744106853064683978216769/43569861897096863762175000000000:ℝ),(59699165982985330449480949946816663120827/130709585691290591286525000000000:ℝ),(295816699827391342613781000766306775822/1276460797766509680532470703125:ℝ),(3881365030313165564382182541634592272/1276460797766509680532470703125:ℝ)]]
theorem row158_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (242585314394572847773886408852162017/155942609949389622668924289024000000000000:ℝ) row158_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row158_coefficients,Fin.sum_univ_succ]
 ring
theorem row158_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row158_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row158_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row158_pos
