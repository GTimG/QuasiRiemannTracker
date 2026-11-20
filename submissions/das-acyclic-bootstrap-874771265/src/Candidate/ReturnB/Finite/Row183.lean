/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row183_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4948724969402578568044254660134777813/816924416819685366796875000000:ℝ),(2304200008258280793422046032859953147/163384883363937073359375000000:ℝ),(330453894471088420905834099377982413/32676976672787414671875000000:ℝ),(562940202414449996125925034996940801/272308138939895122265625000000:ℝ)],
![(6771724898861751095674133821753356583/510577760512303354248046875000:ℝ),(64137364839630831694654454657796062321/2042311042049213416992187500000:ℝ),(189398233135991792797768294583048730307/8169244168196853667968750000000:ℝ),(13730404221677754426097842885465437117/2723081389398951222656250000000:ℝ)],
![(1241052164425305529335416685415950710467/163384883363937073359375000000000:ℝ),(1508593019724953743534153192977961758427/81692441681968536679687500000000:ℝ),(9299843928257450039923389252851178614407/653539533455748293437500000000000:ℝ),(731698962965296725951487941502296837953/217846511151916097812500000000000:ℝ)]]
theorem row183_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (562940202414449996125925034996940801/4158416181978573012624998400000000000000:ℝ) row183_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row183_coefficients,Fin.sum_univ_succ]
 ring
theorem row183_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row183_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row183_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row183_pos
