/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row139_coefficients : Fin 3 → Fin 4 → ℝ := ![![(955744515083322890041708655387/87444592620363802617187500:ℝ),(6637269219437341410897639328289/262333777861091407851562500:ℝ),(244124010256499697115051378496/13116688893054570392578125:ℝ),(277039561797567709170683239448/65583444465272851962890625:ℝ)],
![(104975815916731674455884811846/4372229631018190130859375:ℝ),(3651573599642058721891678766362/65583444465272851962890625:ℝ),(2692496880206916851330561829104/65583444465272851962890625:ℝ),(613222546360005774543092740432/65583444465272851962890625:ℝ)],
![(307125323642000349299371488452/21861148155090950654296875:ℝ),(2175560925659031049575237045596/65583444465272851962890625:ℝ),(1648178880316983346798826432824/65583444465272851962890625:ℝ),(392718667608047451448578852584/65583444465272851962890625:ℝ)]]
theorem row139_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (34629945224695963646335404931/15282050191915099115520000000000:ℝ) row139_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row139_coefficients,Fin.sum_univ_succ]
 ring
theorem row139_pos {δ p : ℝ} (hd : δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row139_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row139_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row139_pos
