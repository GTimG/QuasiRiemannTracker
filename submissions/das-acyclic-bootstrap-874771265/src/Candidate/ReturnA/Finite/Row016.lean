/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row016_coefficients : Fin 3 → Fin 4 → ℝ := ![![(92334732647692441837325564494608563989/311454089074907058164062500:ℝ),(826801349199855353414250593168173047167/934362267224721174492187500:ℝ),(205649596347392451691993984419903588352/233590566806180293623046875:ℝ),(68200307374107050143136629190222999552/233590566806180293623046875:ℝ)],
![(9149661493135479446735777043728064613/15572704453745352908203125:ℝ),(58519209871126693072769815143853464253/33370080972311470517578125:ℝ),(407538317845597283011296659617205215232/233590566806180293623046875:ℝ),(135148768811409319094624510344276934656/233590566806180293623046875:ℝ)],
![(3237931649901547640324388308137006507/11123360324103823505859375:ℝ),(202942207679255160760144442935280055623/233590566806180293623046875:ℝ),(40379359600891811777783806769438867456/46718113361236058724609375:ℝ),(66951153798844474285778591023416418304/233590566806180293623046875:ℝ)]]
theorem row016_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (8172748266460507114963206912038137/55736880282591529543925760000000000:ℝ) row016_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row016_coefficients,Fin.sum_univ_succ]
 ring
theorem row016_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row016_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row016_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row016_pos
