/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row162_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22491843698174245414090273089603284883529/16338488336393707335937500000000:ℝ),(261951912129827951476407519537378610394023/81692441681968536679687500000000:ℝ),(186918598660860276516501518419592001717503/81692441681968536679687500000000:ℝ),(11089043618548282568860138482343117627/24205167905768455312500000000:ℝ)],
![(22554242001410500503189006288567684313009/8169244168196853667968750000000:ℝ),(262316977610824602653078949528073466559271/40846220840984268339843750000000:ℝ),(186715183028229199380039294504559235583161/40846220840984268339843750000000:ℝ),(825978448027738037993216866082628506143/907693796466317074218750000000:ℝ)],
![(23014427269196173178617889076361761879343/16338488336393707335937500000000:ℝ),(268639919592657966877901963493597109529287/81692441681968536679687500000000:ℝ),(384921461862313449543618961522269712096129/163384883363937073359375000000000:ℝ),(1728558220072656970956541092403970141383/3630775185865268296875000000000:ℝ)]]
theorem row162_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (825978448027738037993216866082628506143/28388121135640391766186655744000000000000000:ℝ) row162_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row162_coefficients,Fin.sum_univ_succ]
 ring
theorem row162_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row162_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row162_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row162_pos
