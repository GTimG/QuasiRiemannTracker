/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row188_coefficients : Fin 3 → Fin 4 → ℝ := ![![(793649156244295829343501721841192791/124336825891815872835000000000000:ℝ),(931807567632122525259306292335314897/74602095535089523701000000000000:ℝ),(48188510609307056044769094880348699/7285360892098586298925781250000:ℝ),(28604783732086653094306802630407387/58282887136788690391406250000000:ℝ)],
![(1263812789836924085962942326125641607/77710516182384920521875000000000:ℝ),(7928331334042656421638501339586150133/233131548547154761565625000000000:ℝ),(121938049420443412676049958504179367/5828288713678869039140625000000:ℝ),(91540429169235823919053936309587421/29141443568394345195703125000000:ℝ)],
![(420364467607313355522536390049788729/38855258091192460260937500000000:ℝ),(2823090032362246427602529308103199311/116565774273577380782812500000000:ℝ),(984923813464645159263095284057571711/58282887136788690391406250000000:ℝ),(202792919749223921662922603015030149/58282887136788690391406250000000:ℝ)]]
theorem row188_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (28604783732086653094306802630407387/108647176288613933894860800000000000000:ℝ) row188_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row188_coefficients,Fin.sum_univ_succ]
 ring
theorem row188_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row188_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row188_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row188_pos
