/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row100_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24842036830929098236352796740322208/656617698989932458427734375:ℝ),(499248961927626810078428030541782368/4596323892929527208994140625:ℝ),(68170472448271498177375451174042624/656617698989932458427734375:ℝ),(151837186073470802713588454858771456/4596323892929527208994140625:ℝ)],
![(48649878190009756127630463655533128/656617698989932458427734375:ℝ),(975810577790603151956705780783845112/4596323892929527208994140625:ℝ),(930747574441513648420901601849665536/4596323892929527208994140625:ℝ),(59096647845340067408848500830910464/919264778585905441798828125:ℝ)],
![(9628097843225458889880729873299233/262647079595972983371093750:ℝ),(964082001286390839727068751224481763/9192647785859054417988281250:ℝ),(459002770972105851518883471217146368/4596323892929527208994140625:ℝ),(20778856271255465059665929300913152/656617698989932458427734375:ℝ)]]
theorem row100_identity (δ p : ℝ) : rowMargin .oldSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (20291851827397915097330009082923/9792192858112958827069440000000000:ℝ) row100_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row100_coefficients,Fin.sum_univ_succ]
 ring
theorem row100_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .C δ p := by
 rw [row100_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row100_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row100_pos
