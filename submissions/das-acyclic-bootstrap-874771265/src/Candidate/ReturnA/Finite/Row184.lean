/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row184_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16270771941599329157302113908638174619/4084674552852830977703906250000:ℝ),(32837636656616868915238441593097256843/4084674552852830977703906250000:ℝ),(5370874174253894422043860037438796128/1276460797766509680532470703125:ℝ),(193335694232695172312815756855879808/1276460797766509680532470703125:ℝ)],
![(3624901373134293116481744408955684904311/408467455285283097770390625000000:ℝ),(303336903072772215789675254518685862079/16338698211411323910815625000000:ℝ),(68101147508459292646173028807244808248/6382303988832548402662353515625:ℝ),(6245222820954240525754984639123825472/6382303988832548402662353515625:ℝ)],
![(172368945942452583097856007420000970831399/32677396422822647821631250000000000:ℝ),(54482434403732585347560769089559659291313/4668199488974663974518750000000000:ℝ),(485087162190493306024869380190310502071/63823039888325484026623535156250:ℝ),(1097822408731286411672779399214363884/911757712690364057523193359375:ℝ)]]
theorem row184_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1510435111192931033693873100436561/152287705028700803387621376000000000000:ℝ) row184_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row184_coefficients,Fin.sum_univ_succ]
 ring
theorem row184_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row184_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row184_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row184_pos
