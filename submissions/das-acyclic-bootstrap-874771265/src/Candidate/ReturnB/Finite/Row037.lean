/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row037_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6836450081749799609894300591/53328438687401804179687500:ℝ),(5404924786514401883701158563/15801018870341275312500000:ℝ),(129259839969993938146783525943/426627509499214433437500000:ℝ),(1265816518833796502575221649/14220916983307147781250000:ℝ)],
![(2191047580467947780118604987/13332109671850451044921875:ℝ),(1602434355543211659714173471/3950254717585318828125000:ℝ),(177303162754529593356272527/538671097852543476562500:ℝ),(372988137855365512978324661/4266275094992144334375000:ℝ)],
![(3634250278118849244330119357/53328438687401804179687500:ℝ),(205158588403093391653856783/1316751572528439609375000:ℝ),(12280912106964960083206130179/106656877374803608359375000:ℝ),(288759117946250475915396947/10665687737480360835937500:ℝ)]]
theorem row037_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (288759117946250475915396947/4854072996968839776000000000:ℝ) row037_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row037_coefficients,Fin.sum_univ_succ]
 ring
theorem row037_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row037_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row037_pos
