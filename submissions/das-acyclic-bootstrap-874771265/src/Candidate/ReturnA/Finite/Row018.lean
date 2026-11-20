/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row018_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22872816358007194347066821228305981357/77863522268726764541015625:ℝ),(40961572191504481708661874115480495579/46718113361236058724609375:ℝ),(203762451282726306672083961489316759552/233590566806180293623046875:ℝ),(67573038224933556880166900237457225728/233590566806180293623046875:ℝ)],
![(45328368348958658424996193551889730747/77863522268726764541015625:ℝ),(81173133635133657419503784203678163453/46718113361236058724609375:ℝ),(403780180728773448110709331055816978432/233590566806180293623046875:ℝ),(133899615236146743237266472177470353408/233590566806180293623046875:ℝ)],
![(17965159389206408628682077108443690297/62290817814981411632812500:ℝ),(160852706479582420926822348529069925611/186872453444944234898437500:ℝ),(40005161190460273801648345643278585856/46718113361236058724609375:ℝ),(13265853874551078338278056361875122176/46718113361236058724609375:ℝ)]]
theorem row018_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (6477467712183143719862332207946837/44589504226073223635140608000000000:ℝ) row018_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row018_coefficients,Fin.sum_univ_succ]
 ring
theorem row018_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row018_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row018_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row018_pos
