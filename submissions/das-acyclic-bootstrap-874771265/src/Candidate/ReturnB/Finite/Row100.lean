/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row100_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6955718209473396069662473769248288/183851751581252498759765625:ℝ),(19969808882562549496673069033752864/183851751581252498759765625:ℝ),(19087589313864549949774293156260864/183851751581252498759765625:ℝ),(6073441962635288553150385391756288/183851751581252498759765625:ℝ)],
![(13621861018633316911696517569845608/183851751581252498759765625:ℝ),(39032122327482024855711890234119976/183851751581252498759765625:ℝ),(37229615845232571863630093707184128/183851751581252498759765625:ℝ),(2363847669239328516381486083581952/36770350316250499751953125:ℝ)],
![(2695846027680913671790089164246533/73540700632500999503906250:ℝ),(38562973789636249339597456011443249/367703503162504997519531250:ℝ),(18359964744473735612485309925214464/183851751581252498759765625:ℝ),(5818033371386944186586818384796672/183851751581252498759765625:ℝ)]]
theorem row100_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (5681673214245062682213689828903/2741796042895124197539840000000000:ℝ) row100_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row100_coefficients,Fin.sum_univ_succ]
 ring
theorem row100_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row100_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row100_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row100_pos
