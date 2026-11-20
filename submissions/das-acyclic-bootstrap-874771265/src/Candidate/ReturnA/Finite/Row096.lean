/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row096_coefficients : Fin 3 → Fin 4 → ℝ := ![![(364679846277156141703928474267/104933511144436563140625000:ℝ),(894204316223071867630795455401/104933511144436563140625000:ℝ),(713153628366873690650655344251/104933511144436563140625000:ℝ),(183274920094317438703475863117/104933511144436563140625000:ℝ)],
![(2018047658514729321272890603951/262333777861091407851562500:ℝ),(4871918605085667959567683612381/262333777861091407851562500:ℝ),(3800223435304278157120970596409/262333777861091407851562500:ℝ),(944227058773496362704302587979/262333777861091407851562500:ℝ)],
![(2782510838719155078890070270367/524667555722182815703125000:ℝ),(6918007226956388121022465159357/524667555722182815703125000:ℝ),(5618503369164595150098860983013/524667555722182815703125000:ℝ),(1480456464975550320620216094023/524667555722182815703125000:ℝ)]]
theorem row096_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (183274920094317438703475863117/48902560614128317169664000000000:ℝ) row096_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row096_coefficients,Fin.sum_univ_succ]
 ring
theorem row096_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row096_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row096_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row096_pos
