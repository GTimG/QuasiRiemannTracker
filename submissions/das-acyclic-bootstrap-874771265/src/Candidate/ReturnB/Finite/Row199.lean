/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row199_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137040111874893143442603955259/15337260259537587890625:ℝ),(115149421536812215812454320233/5112420086512529296875:ℝ),(280838925493498617957309527296/15337260259537587890625:ℝ),(24143590919318371320850173952/5112420086512529296875:ℝ)],
![(253794940004782867286018543284/15337260259537587890625:ℝ),(208526582774841565949471358524/5112420086512529296875:ℝ),(163981206376951124574859224064/5112420086512529296875:ℝ),(120158810811111543162182139904/15337260259537587890625:ℝ)],
![(999513642316619493070891804/122698082076300703125:ℝ),(3760300951359852575534249708/189348892093056640625:ℝ),(235457747667109799588310250496/15337260259537587890625:ℝ),(55812575896539177603897499648/15337260259537587890625:ℝ)]]
theorem row199_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (6813058581120505078600769/28590725358053130240000000000:ℝ) row199_coefficients (111/256:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row199_coefficients,Fin.sum_univ_succ]
 ring
theorem row199_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row199_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row199_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row199_pos
