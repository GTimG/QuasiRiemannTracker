/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row045_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24409925116947595485426547841879/15810662953125000000000:ℝ),(218509151987665261948481659171333/47431988859375000000000:ℝ),(47163967593079751154944226968/10293400360107421875:ℝ),(140726925843923862948790980904/92640603240966796875:ℝ)],
![(11832616928078574892598052449137/3952665738281250000000:ℝ),(105903544144801013068074390864467/11857997214843750000000:ℝ),(822772296616851888377003486528/92640603240966796875:ℝ),(272727817237435572827939162176/92640603240966796875:ℝ)],
![(5734118416989808577005954025351/3952665738281250000000:ℝ),(51312107300988906853116856452757/11857997214843750000000:ℝ),(398576725890808564548163390352/92640603240966796875:ℝ),(44031429333343789427254998928/30880201080322265625:ℝ)]]
theorem row045_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (2751964333333986839203437433/29473211940864000000000000000:ℝ) row045_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row045_coefficients,Fin.sum_univ_succ]
 ring
theorem row045_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row045_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row045_pos
