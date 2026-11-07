/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row199_coefficients : Fin 3 → Fin 4 → ℝ := ![![(411140055779047247113467447314/46011787588325478515625:ℝ),(1036403707175038528520616244754/46011787588325478515625:ℝ),(842575442752607182574231113216/46011787588325478515625:ℝ),(217311791356615901167082315776/46011787588325478515625:ℝ)],
![(761423478252093337082069964664/46011787588325478515625:ℝ),(1876854724493805246181676392312/46011787588325478515625:ℝ),(1475945841818307414699005560832/46011787588325478515625:ℝ),(360514595576595505599399133184/46011787588325478515625:ℝ)],
![(14993462393762599495593988616/1840471503533019140625:ℝ),(913809715015912964968676817608/46011787588325478515625:ℝ),(706429578797076835445604284416/46011787588325478515625:ℝ),(167456423625228857866777182208/46011787588325478515625:ℝ)]]
theorem row199_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (10220728981032034781907787/42886094384191979520000000000:ℝ) row199_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row199_coefficients,Fin.sum_univ_succ]
 ring
theorem row199_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row199_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row199_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row199_pos
