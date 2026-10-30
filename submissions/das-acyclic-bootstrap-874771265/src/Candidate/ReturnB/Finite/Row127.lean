/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row127_coefficients : Fin 3 → Fin 4 → ℝ := ![![(344658227488000284626851716770713423/73540700632500999503906250:ℝ),(5057454601431885912880435791054946817/367703503162504997519531250:ℝ),(4945981534837778318568753628448027689/367703503162504997519531250:ℝ),(1611816302204531759630793004684147987/367703503162504997519531250:ℝ)],
![(1711673612308614589052031093336127739/183851751581252498759765625:ℝ),(5022001611534138086582788081058943521/183851751581252498759765625:ℝ),(196397347232950107358255700820122941/7354070063250099950390625:ℝ),(1599603901762934445909853486999007743/183851751581252498759765625:ℝ)],
![(1701231643337905568368862468578992563/367703503162504997519531250:ℝ),(39920522747812769398958463393169861/2941628025300039980156250:ℝ),(4877392634381847458673922853818348411/367703503162504997519531250:ℝ),(1588557143143081765198234706610483349/367703503162504997519531250:ℝ)]]
theorem row127_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1588557143143081765198234706610483349/718745381868699437639883816960000000000:ℝ) row127_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row127_coefficients,Fin.sum_univ_succ]
 ring
theorem row127_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row127_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row127_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row127_pos
