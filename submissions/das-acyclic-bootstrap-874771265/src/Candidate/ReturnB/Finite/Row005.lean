/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(46368462385660011822581/79053313710937500:ℝ),(1659951951975814410531/975966835937500:ℝ),(129850363533525451522349/79053313710937500:ℝ),(41762717809144496091919/79053313710937500:ℝ)],
![(3022753399565253709147/2874665953125000:ℝ),(480309259094273311209349/158106627421875000:ℝ),(38504384637133963940159/13175552285156250:ℝ),(12332899460618600839637/13175552285156250:ℝ)],
![(394911078659672674547621/843235346250000000:ℝ),(3408377539176074669830447/2529706038750000000:ℝ),(20401147345617761980199/15810662742187500:ℝ),(32516852253180789707633/79053313710937500:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (32516852253180789707633/147366057738240000000000:ℝ) row005_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ]
 ring
theorem row005_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row005_pos
