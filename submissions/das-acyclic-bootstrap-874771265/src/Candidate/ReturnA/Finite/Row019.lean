/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row019_coefficients : Fin 3 → Fin 4 → ℝ := ![![(90651386365427879490207184668456217117/311454089074907058164062500:ℝ),(811693837172474631755282934781489518743/934362267224721174492187500:ℝ),(28840483163706000112647789464346843136/33370080972311470517578125:ℝ),(66948461437302268951487881154053935104/233590566806180293623046875:ℝ)],
![(6415746186681614698830370221921086222/11123360324103823505859375:ℝ),(402113016609525081097178417695028756134/233590566806180293623046875:ℝ),(400038195467713291482843177877824684032/233590566806180293623046875:ℝ),(3790167039541959372813995821411106816/6674016194462294103515625:ℝ)],
![(22248273960970879727184019448304412756/77863522268726764541015625:ℝ),(199197633197738570762676069220005444092/233590566806180293623046875:ℝ),(39632577965605103652785002055457898496/46718113361236058724609375:ℝ),(65710077308208514431292682464697286656/233590566806180293623046875:ℝ)]]
theorem row019_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2005312417853043042947164381857217/13934220070647882385981440000000000:ℝ) row019_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row019_coefficients,Fin.sum_univ_succ]
 ring
theorem row019_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row019_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row019_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row019_pos
