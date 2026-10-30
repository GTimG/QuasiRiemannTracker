/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row129_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44140828217963625403488832425771479/2451356687750033316796875:ℝ),(9709437456918473768180358562101291433/183851751581252498759765625:ℝ),(9489080491226603430851280271729980416/183851751581252498759765625:ℝ),(3090201590949388249333539041678737408/183851751581252498759765625:ℝ)],
![(2199288357877697938696922188597352404/61283917193750832919921875:ℝ),(19347908859924178429660198110390274316/183851751581252498759765625:ℝ),(18906017417584240630080556198185988096/183851751581252498759765625:ℝ),(6155966489422416361530075178744020992/183851751581252498759765625:ℝ)],
![(1095961926065564742444588167502501404/61283917193750832919921875:ℝ),(9640214924684878355842856039548715908/183851751581252498759765625:ℝ),(1883735104612793427183550248851378176/36770350316250499751953125:ℝ),(3066342794375632833459174323934429184/183851751581252498759765625:ℝ)]]
theorem row129_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (93577355785389185591405466428663/43868736686321987160637440000000000:ℝ) row129_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row129_coefficients,Fin.sum_univ_succ]
 ring
theorem row129_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row129_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row129_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row129_pos
