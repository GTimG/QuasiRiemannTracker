/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row129_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1103529093759655997394104614471415153/61284318572393696119921875:ℝ),(242737782373701605818336705241496704971/4596323892929527208994140625:ℝ),(33889831014686558582687858328815814656/656617698989932458427734375:ℝ),(77255627768440489615488011188538884096/4596323892929527208994140625:ℝ)],
![(54982628351782848653384303472683979148/1532107964309842402998046875:ℝ),(69100201854750494480855545012672815356/656617698989932458427734375:ℝ),(472654044348847411472457785322169802752/4596323892929527208994140625:ℝ),(21985762553456959920327408934591004672/656617698989932458427734375:ℝ)],
![(27399257891770499190113635848612876548/1532107964309842402998046875:ℝ),(241007219038259616791503107943160142796/4596323892929527208994140625:ℝ),(47093738509932435361609061320105910272/919264778585905441798828125:ℝ),(76659157631722699595499911000083038208/4596323892929527208994140625:ℝ)]]
theorem row129_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2339451832022787463241574432375581/1096725600108651388631777280000000000:ℝ) row129_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row129_coefficients,Fin.sum_univ_succ]
 ring
theorem row129_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row129_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row129_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row129_pos
