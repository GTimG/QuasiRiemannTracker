/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row206_coefficients : Fin 3 → Fin 4 → ℝ := ![![(62205915010451648778283009016995679001736/362554294719123619498601455078125:ℝ),(165507070431750050882523812288511720897544/362554294719123619498601455078125:ℝ),(28922065666244388996827146930281315335836/72510858943824723899720291015625:ℝ),(41308759350135676049830763165074128533372/362554294719123619498601455078125:ℝ)],
![(122042961701719075054028091740612868707888/362554294719123619498601455078125:ℝ),(323287884299342039937440234475807973609424/362554294719123619498601455078125:ℝ),(280880098933538777762846856935286603971584/362554294719123619498601455078125:ℝ),(79634338474527407353590425349294624070048/362554294719123619498601455078125:ℝ)],
![(60952968493870540919572200791565164626552/362554294719123619498601455078125:ℝ),(32223722912248900969843300495073126032136/72510858943824723899720291015625:ℝ),(139597639985678942377808954598558368408504/362554294719123619498601455078125:ℝ),(39431569546952409415594168951367277874376/362554294719123619498601455078125:ℝ)]]
theorem row206_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (4928946193369051176949271118920909734297/22146259041322402866170896601579520000000000:ℝ) row206_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row206_coefficients,Fin.sum_univ_succ]
 ring
theorem row206_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row206_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row206_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row206_pos
