/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(23184232625361677934479/39526657382812500:ℝ),(201684174824988448165147/118579972148437500:ℝ),(194775557720406022116773/118579972148437500:ℝ),(62644080771502607755063/118579972148437500:ℝ)],
![(16625144800975347976363/15810662953125000:ℝ),(720463937354523863546173/237159944296875000:ℝ),(173269742803266867927029/59289986074218750:ℝ),(55498051468293456951847/59289986074218750:ℝ)],
![(592366660409378843890717/1264853036250000000:ℝ),(5112566682954401346861719/3794559108750000000:ℝ),(30601723308062932257343/23715994429687500:ℝ),(48775282111368885812041/118579972148437500:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (48775282111368885812041/221049089556480000000000:ℝ) row005_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ]
 ring
theorem row005_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row005_pos
