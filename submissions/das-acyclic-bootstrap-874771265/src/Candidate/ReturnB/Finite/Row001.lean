/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12600933602938825613494092533/189612226444095303750000000:ℝ),(99420877162093605348804993917/568836679332285911250000000:ℝ),(85433351897737780176163155037/568836679332285911250000000:ℝ),(23815275544460651667840438719/568836679332285911250000000:ℝ)],
![(8974956273249503337447816701/94806113222047651875000000:ℝ),(66238772949174707572655576681/284418339666142955625000000:ℝ),(17613503341737579348898518851/94806113222047651875000000:ℝ),(541064235831461619455337199/11376733586645718225000000:ℝ)],
![(6107427849336562276401540869/189612226444095303750000000:ℝ),(8275912798612817542171043149/113767335866457182250000000:ℝ),(29757189847951192678019348819/568836679332285911250000000:ℝ),(2205134737474391003789585227/189612226444095303750000000:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2205134737474391003789585227/10786828882152977280000000000:ℝ) row001_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ]
 ring
theorem row001_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row001_pos
