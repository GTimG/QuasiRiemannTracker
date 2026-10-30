/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row175_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25317337010451959995684974545314607554277/108923255575958048906250000000000:ℝ),(30255908729756601831959679651200429865527/65353953345574829343750000000000:ℝ),(73728179463930816161113091252838829127/319111100320189596405029296875:ℝ),(164621310799471498376150919745823656/319111100320189596405029296875:ℝ)],
![(12850412366803343612604521767571502763111/27230813893989512226562500000000:ℝ),(77075548061111914159452395656535105275073/81692441681968536679687500000000:ℝ),(151941908440714888962091349479426753444/319111100320189596405029296875:ℝ),(1453270293591935770229053605842017904/319111100320189596405029296875:ℝ)],
![(6603950398471482277502059295582367153053/27230813893989512226562500000000:ℝ),(7999856143119036431434332321437223627551/16338488336393707335937500000000:ℝ),(81109799585733692779140147200984199332/319111100320189596405029296875:ℝ),(2251119085625679519903572312835409816/319111100320189596405029296875:ℝ)]]
theorem row175_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (20577663849933937297018864968227957/77970303412098243986718720000000000000000:ℝ) row175_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row175_coefficients,Fin.sum_univ_succ]
 ring
theorem row175_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row175_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row175_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row175_pos
