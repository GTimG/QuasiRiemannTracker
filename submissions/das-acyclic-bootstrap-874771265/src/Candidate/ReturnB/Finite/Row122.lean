/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row122_coefficients : Fin 3 → Fin 4 → ℝ := ![![(224581821625566527437527587644700602/183851751581252498759765625:ℝ),(660273634735617060573237417919327258/183851751581252498759765625:ℝ),(4173642174138454252189924657395397/1186140332782274185546875:ℝ),(211222513853476938358830160488847379/183851751581252498759765625:ℝ)],
![(441003768364084011035823698510073116/183851751581252498759765625:ℝ),(1295787330841948378828315874674068068/183851751581252498759765625:ℝ),(1268791531831667182212913207299637888/183851751581252498759765625:ℝ),(414007543842665953838549087541892936/183851751581252498759765625:ℝ)],
![(217009724818856390297825543745524614/183851751581252498759765625:ℝ),(127454411405286855109482446659277402/36770350316250499751953125:ℝ),(623630398626266977788420606033465878/183851751581252498759765625:ℝ),(203367850900061331984379295701353482/183851751581252498759765625:ℝ)]]
theorem row122_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (101683925450030665992189647850676741/44921586366793714852492738560000000000:ℝ) row122_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row122_coefficients,Fin.sum_univ_succ]
 ring
theorem row122_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row122_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row122_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row122_pos
