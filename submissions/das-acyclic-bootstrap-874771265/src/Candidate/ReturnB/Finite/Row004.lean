/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3503665815212221642443642167863/23701528305511912968750000:ℝ),(30152829725567775535840846793839/71104584916535738906250000:ℝ),(872759500832186038100959958767/2154684391410173906250000:ℝ),(832642021559098310113796213551/6464053174230521718750000:ℝ)],
![(2866955762963907625227612853399/11850764152755956484375000:ℝ),(24487941886686435947174684372527/35552292458267869453125000:ℝ),(23204227140898996565100649753463/35552292458267869453125000:ℝ),(7316941280128099446646303941133/35552292458267869453125000:ℝ)],
![(459650566330353090156257555507/4740305661102382593750000:ℝ),(3888445882600285665615654377363/14220916983307147781250000:ℝ),(3646635406191607991336525173913/14220916983307147781250000:ℝ),(379029468946111861483006154357/4740305661102382593750000:ℝ)]]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (379029468946111861483006154357/2209142555064929746944000000000:ℝ) row004_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row004_coefficients,Fin.sum_univ_succ]
 ring
theorem row004_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row004_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row004_pos
