/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row214_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7361372423775841264409936682034335573842/72510858943824723899720291015625:ℝ),(87698503277039061856456845441748796050186/362554294719123619498601455078125:ℝ),(65431454953216077840258683957361385006592/362554294719123619498601455078125:ℝ),(14538050393977277908676241669624110575616/362554294719123619498601455078125:ℝ)],
![(74416409411216250323248782831933702065024/362554294719123619498601455078125:ℝ),(25352903497965267035344564074041751807104/51793470674160517071228779296875:ℝ),(18943858244372369623448164830889649446912/51793470674160517071228779296875:ℝ),(5909908730552486509257577900223797108736/72510858943824723899720291015625:ℝ)],
![(37749037517662433331677489180255521060864/362554294719123619498601455078125:ℝ),(12883971529450681192584993410440045766656/51793470674160517071228779296875:ℝ),(67589057778221474417712515147651133550592/362554294719123619498601455078125:ℝ),(15148508937752517567993868754826334244864/362554294719123619498601455078125:ℝ)]]
theorem row214_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (3549328709467108864422910563873073871/21627206095041409048995016212480000000000:ℝ) row214_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row214_coefficients,Fin.sum_univ_succ]
 ring
theorem row214_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row214_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row214_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row214_pos
