/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row099_coefficients : Fin 3 → Fin 4 → ℝ := ![![(740751135380095180456346892122268797/18385295571718108835976562500:ℝ),(2129475902755806344194696242894870391/18385295571718108835976562500:ℝ),(2038228029739637612462050124148934391/18385295571718108835976562500:ℝ),(30928456883366676205113132065539657/875490265319909944570312500:ℝ)],
![(728246117553606839925584546885817917/9192647785859054417988281250:ℝ),(2089951752333897459698567245500068599/9192647785859054417988281250:ℝ),(1996730302233669559876039779439025447/9192647785859054417988281250:ℝ),(6047798647093543195012609103093093/87549026531990994457031250:ℝ)],
![(103316219625929928669511133315804291/2626470795959729833710937500:ℝ),(2072718951760738504827289362586020007/18385295571718108835976562500:ℝ),(1977398781435967403364261438278647253/18385295571718108835976562500:ℝ),(29899400586212741522911835989440823/875490265319909944570312500:ℝ)]]
theorem row099_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (29899400586212741522911835989440823/13369607315610226451892142080000000000:ℝ) row099_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row099_coefficients,Fin.sum_univ_succ]
 ring
theorem row099_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row099_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row099_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row099_pos
