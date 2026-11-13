/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row175_coefficients : Fin 3 → Fin 4 → ℝ := ![![(180852743916298650695830305066525393285739/778033248162443995753125000000000:ℝ),(216138224712140129839646327040428445185941/466819948897466397451875000000000:ℝ),(1053483107433856584595915222963013382674/4558788563451820287615966796875:ℝ),(677786508526339116956436565652421904/1276460797766509680532470703125:ℝ)],
![(642572075679078130076257672769903745045311/1361558184284276992567968750000000:ℝ),(770842005380444734004082735946429435867841/816934910570566195540781250000000:ℝ),(2171047788902408812105906112413215929272/4558788563451820287615966796875:ℝ),(29259372657581102412732434811111299296/6382303988832548402662353515625:ℝ)],
![(330223452087019810761369671450184040088677/1361558184284276992567968750000000:ℝ),(400036412805487595284595033558329628785051/816934910570566195540781250000000:ℝ),(8112564312596750206951713410510389523528/31911519944162742013311767578125:ℝ),(45120140205575328568098651500098155824/6382303988832548402662353515625:ℝ)]]
theorem row175_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (42361656782896194809777285353276369/155942609949389622668924289024000000000000:ℝ) row175_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row175_coefficients,Fin.sum_univ_succ]
 ring
theorem row175_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row175_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row175_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row175_pos
