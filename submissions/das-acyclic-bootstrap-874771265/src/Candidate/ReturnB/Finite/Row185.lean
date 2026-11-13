/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row185_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2393697905734106991832546316522504241533/339716382930416138906250000000000:ℝ),(1139152535841040209473576769645924254579/67943276586083227781250000000000:ℝ),(4238977573349725872720500599055403079433/339716382930416138906250000000000:ℝ),(312269010082351933872159918085362536857/113238794310138712968750000000000:ℝ)],
![(2731639102941627521198878753533232812677/169858191465208069453125000000000:ℝ),(6665246027995217314956720695314285920223/169858191465208069453125000000000:ℝ),(5164788972888513335645914222873372701539/169858191465208069453125000000000:ℝ),(410357899485411972061189141259453406331/56619397155069356484375000000000:ℝ)],
![(640853410998437417428687218216242756881/67943276586083227781250000000000:ℝ),(8036426743001466095301156817529209095199/339716382930416138906250000000000:ℝ),(6489950458499313978801123606038296146311/339716382930416138906250000000000:ℝ),(552559926147858158673091984195252361839/113238794310138712968750000000000:ℝ)]]
theorem row185_identity (δ p : ℝ) : rowMargin .newTop .P δ p =
 Record12518109.Bernstein.bsum 2 3 (312269010082351933872159918085362536857/1729269042490725878841999360000000000000000:ℝ) row185_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row185_coefficients,Fin.sum_univ_succ]
 ring
theorem row185_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .P δ p := by
 rw [row185_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row185_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row185_pos
