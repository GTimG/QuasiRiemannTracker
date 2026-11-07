/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row183_coefficients : Fin 3 → Fin 4 → ℝ := ![![(247445005399801050441922869710361697969/40846745528528309777039062500000:ℝ),(115214734900509758936720594842048353631/8169349105705661955407812500000:ℝ),(413088484128970491197225866286827520209/40846745528528309777039062500000:ℝ),(4021296705510465168738839126327854763/1945083120406109989382812500000:ℝ)],
![(48371102913690812119269179835092569007/3647030850761456230092773437500:ℝ),(3206992573714819791599537563313373150421/102116863821320774442597656250000:ℝ),(9470356345970041922378254044757155103871/408467455285283097770390625000000:ℝ),(98080552434705840756744479061226141951/19450831204061099893828125000000:ℝ)],
![(62054578077256324250663985638143755519743/8169349105705661955407812500000000:ℝ),(75432330300724340607061304418673482009947/4084674552852830977703906250000000:ℝ),(465011462187930945883397419052695899148403/32677396422822647821631250000000000:ℝ),(5226693098201607841631028260628739709419/1556066496324887991506250000000000:ℝ)]]
theorem row183_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (4021296705510465168738839126327854763/29703354276074213841699864576000000000000:ℝ) row183_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row183_coefficients,Fin.sum_univ_succ]
 ring
theorem row183_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row183_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row183_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row183_pos
