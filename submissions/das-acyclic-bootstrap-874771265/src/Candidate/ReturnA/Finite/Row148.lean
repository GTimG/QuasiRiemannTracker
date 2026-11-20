/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row148_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3867635311447231011113712952721/2879923865976562500000000:ℝ),(389907732642717549936886109992381/129596573968945312500000000:ℝ),(8186986353398575745915258655247/4049892936529541015625000:ℝ),(1441231865036320919766226557749/4049892936529541015625000:ℝ)],
![(70565856966089701885275799408049/28799238659765625000000000:ℝ),(1357980629836230498978906569342521/259193147937890625000000000:ℝ),(1294124294629893765708450588983/404989293652954101562500:ℝ),(164611924096420043815600003561/404989293652954101562500:ℝ)],
![(90208071081259658289160753089791/76797969759375000000000000:ℝ),(1008123763165703622126608086227809/414709036700625000000000000:ℝ),(694843894333656067271961688292/506236617066192626953125:ℝ),(470858778429976395937998002987/4049892936529541015625000:ℝ)]]
theorem row148_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (470858778429976395937998002987/7730736762087014400000000000000000:ℝ) row148_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row148_coefficients,Fin.sum_univ_succ]
 ring
theorem row148_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row148_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row148_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row148_pos
