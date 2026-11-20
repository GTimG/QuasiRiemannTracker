/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row076_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4835248105476072410177562915289/65583444465272851962890625:ℝ),(13144904574372381416282646407561/65583444465272851962890625:ℝ),(4743119363778688289997996268267/26233377786109140785156250:ℝ),(2364949738625976435799182910597/43722296310181901308593750:ℝ)],
![(8765152148359491919644838452854/65583444465272851962890625:ℝ),(23330674920528412660743808376506/65583444465272851962890625:ℝ),(821102711270596034628525462188/2623337778610914078515625:ℝ),(1986816979042032585840920127016/21861148155090950654296875:ℝ)],
![(887656198156712859639253154243/13116688893054570392578125:ℝ),(2336310858302295829837303952929/13116688893054570392578125:ℝ),(2027374941906729883196760799379/13116688893054570392578125:ℝ),(192847720865942216662851250231/4372229631018190130859375:ℝ)]]
theorem row076_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (192847720865942216662851250231/65203414152171089559552000000000:ℝ) row076_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row076_coefficients,Fin.sum_univ_succ]
 ring
theorem row076_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row076_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row076_pos
