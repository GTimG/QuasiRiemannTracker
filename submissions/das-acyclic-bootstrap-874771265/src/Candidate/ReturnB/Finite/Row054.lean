/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row054_coefficients : Fin 3 → Fin 4 → ℝ := ![![(39564082759860377348768914834284183589267/298993963871901653437500000000:ℝ),(118096948789891292315764098015485553845651/298993963871901653437500000000:ℝ),(41726892326389445487565103309260812736/106176833761328712158203125:ℝ),(152226803533447710150821447339558900032/1167945171374615833740234375:ℝ)],
![(9809029776894194533160659100353863059903/37374245483987706679687500000:ℝ),(29278537554581383293743036289802396921279/37374245483987706679687500000:ℝ),(910322080043419268779354624151474058752/1167945171374615833740234375:ℝ),(301899953683386789493466540301519875584/1167945171374615833740234375:ℝ)],
![(810625200805445469300977824863230247433/6229040913997951113281250000:ℝ),(96780757466132678536941890871235013489/249161636559918044531250000:ℝ),(50149772469104767444959473802448365056/129771685708290648193359375:ℝ),(49893457523338439800863581209367277056/389315057124871944580078125:ℝ)]]
theorem row054_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (97448159225270390236061682049545463/1486307056170397146808320000000000000:ℝ) row054_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row054_coefficients,Fin.sum_univ_succ]
 ring
theorem row054_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row054_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row054_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row054_pos
