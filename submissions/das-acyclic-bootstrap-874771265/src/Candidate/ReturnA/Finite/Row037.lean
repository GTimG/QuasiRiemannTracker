/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row037_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2278816638560709596581425899/17776146703453820156250000:ℝ),(36483241533570209997993021023/106656880220722920937500000:ℝ),(1795275521406876559348629523/5925382234484606718750000:ℝ),(1898724745890497492204173157/21331376044144584187500000:ℝ)],
![(1460698402930466056980627911/8888073351726910078125000:ℝ),(5408216067735360265830702683/13332110027590365117187500:ℝ),(8776506846402199182846950333/26664220055180730234375000:ℝ),(23311759660575386333774287/266642200551807302343750:ℝ)],
![(1211416861810744762379829923/17776146703453820156250000:ℝ),(8308923739267585484770921333/53328440110361460468750000:ℝ),(6140456905026017016012625459/53328440110361460468750000:ℝ),(96253056257332629392079593/3555229340690764031250000:ℝ)]]
theorem row037_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (96253056257332629392079593/1618024375496596608000000000:ℝ) row037_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row037_coefficients,Fin.sum_univ_succ]
 ring
theorem row037_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row037_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row037_pos
