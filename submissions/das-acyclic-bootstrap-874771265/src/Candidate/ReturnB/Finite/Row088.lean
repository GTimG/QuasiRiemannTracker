/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row088_coefficients : Fin 3 → Fin 4 → ℝ := ![![(287957230842752136098404072649622908/61283917193750832919921875:ℝ),(507725419172130169766769058425525716/36770350316250499751953125:ℝ),(2486087523389040702665458952781836288/183851751581252498759765625:ℝ),(811331279944914511747232554071826432/183851751581252498759765625:ℝ)],
![(570289472442645656944067323008711268/61283917193750832919921875:ℝ),(1005215893930470779010056531202301132/36770350316250499751953125:ℝ),(4920455893986628859323637872718737408/183851751581252498759765625:ℝ),(1605243150528206463562219974014615552/183851751581252498759765625:ℝ)],
![(56505303047370191936110007981704867/12256783438750166583984375:ℝ),(497839179094175348115890771028722021/36770350316250499751953125:ℝ),(4469921040924620354764503188509696/337342663451839447265625:ℝ),(158897953297179334615525121362386944/36770350316250499751953125:ℝ)]]
theorem row088_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (19396722814597086745059218916307/8773747337264397432127488000000000:ℝ) row088_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row088_coefficients,Fin.sum_univ_succ]
 ring
theorem row088_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row088_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row088_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row088_pos
