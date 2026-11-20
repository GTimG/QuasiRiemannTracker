/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row165_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5722191129851142976557520823761459729050439/16338488336393707335937500000000:ℝ),(13350462605007935131132182169695023251813817/16338488336393707335937500000000:ℝ),(9539368353209124254532680040797138735006317/16338488336393707335937500000000:ℝ),(2568676947759632915775422959409432054531/21960333785475413085937500000:ℝ)],
![(5719885935487294836760577159588246458815319/8169244168196853667968750000000:ℝ),(106690431851598249152008937511652269839569/65353953345574829343750000000:ℝ),(9517974435245732123686361390188842347944117/8169244168196853667968750000000:ℝ),(20446829660191504747179823455233296566877/87841335141901652343750000000:ℝ)],
![(28714340606310701925447560762627195343380051/81692441681968536679687500000000:ℝ),(66989895362463279571192779056447796127089097/81692441681968536679687500000000:ℝ),(47861929090066945001240068713814766011067609/81692441681968536679687500000000:ℝ),(103079227630538757996824696132677439558291/878413351419016523437500000000:ℝ)]]
theorem row165_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (20446829660191504747179823455233296566877/2813171229957654306636303433728000000000000000:ℝ) row165_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1023/2048:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row165_coefficients,Fin.sum_univ_succ]
 ring
theorem row165_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1023/2048:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row165_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row165_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row165_pos
