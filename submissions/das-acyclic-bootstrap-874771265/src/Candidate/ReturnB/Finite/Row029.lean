/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row029_coefficients : Fin 3 → Fin 4 → ℝ := ![![(76390215365748009858460856087066899/33221551541322405937500000:ℝ),(680657171126999474779481897993266091/99664654623967217812500000:ℝ),(673830728686229094553696662917410091/99664654623967217812500000:ℝ),(74114723284799153300694444395114899/33221551541322405937500000:ℝ)],
![(220934446599862016106622191775117817/49832327311983608906250000:ℝ),(656019219160852807666152103849779499/49832327311983608906250000:ℝ),(649263581227988422175170105769563547/49832327311983608906250000:ℝ),(14278584934657969095462556246326791/3322155154132240593750000:ℝ)],
![(19349243236735056865772652884052467/9060423147633383437500000:ℝ),(210603884617572781648407277229877769/33221551541322405937500000:ℝ),(625126911777098144600547538008493553/99664654623967217812500000:ℝ),(68718966005053042880176830597812461/33221551541322405937500000:ℝ)]]
theorem row029_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (68718966005053042880176830597812461/507326141839495559443906560000000000:ℝ) row029_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row029_coefficients,Fin.sum_univ_succ]
 ring
theorem row029_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row029_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row029_pos
