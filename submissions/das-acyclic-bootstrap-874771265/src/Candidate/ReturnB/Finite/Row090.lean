/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row090_coefficients : Fin 3 → Fin 4 → ℝ := ![![(304969181942893179572841262276994/7354070063250099950390625:ℝ),(21983842409870837696224911544258948/183851751581252498759765625:ℝ),(42219180383482914077423580676678117/367703503162504997519531250:ℝ),(4499948967190672462129503437128307/122567834387501665839843750:ℝ)],
![(2969782044205947753773973551153216/36770350316250499751953125:ℝ),(1378431481161831876314809653119648/5930701663911370927734375:ℝ),(40945903198534075421512912988638936/183851751581252498759765625:ℝ),(4354442327057938494625907374231976/61283917193750832919921875:ℝ)],
![(1459880878317511195093577449502896/36770350316250499751953125:ℝ),(4194089008033085394883643835110288/36770350316250499751953125:ℝ),(4011594623429629819337658101011888/36770350316250499751953125:ℝ),(425791719362011341874976405134832/12256783438750166583984375:ℝ)]]
theorem row090_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (26611982460125708867186025320927/11698329783019196576169984000000000:ℝ) row090_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row090_coefficients,Fin.sum_univ_succ]
 ring
theorem row090_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row090_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row090_pos
