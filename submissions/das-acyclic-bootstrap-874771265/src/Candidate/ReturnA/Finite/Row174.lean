/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row174_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5986886316239373487227992459086753057865423/1633869821141132391081562500000000:ℝ),(59718691415246276520875592377340747027232567/8169349105705661955407812500000000:ℝ),(16624761409449732409918442894970528393416/4558788563451820287615966796875:ℝ),(5592581148176255728278895336686726784/6382303988832548402662353515625:ℝ)],
![(3008114386504055816760660775638369417150091/408467455285283097770390625000000:ℝ),(30022362282193600904424241204098843383883923/2042337276426415488851953125000000:ℝ),(33486593205358163938193511533496970116256/4558788563451820287615966796875:ℝ),(62894082003421143504872504870783280896/6382303988832548402662353515625:ℝ)],
![(217327581400821709582844300160844975745873/58352493612183299681484375000000:ℝ),(15240970910745596447727629845695921256370527/2042337276426415488851953125000000:ℝ),(120346250746064114459861493178155916812128/31911519944162742013311767578125:ℝ),(30185585940036037385397257953155468928/911757712690364057523193359375:ℝ)]]
theorem row174_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (43692040220126997877178869817865053/3118852198987792453378485780480000000000000:ℝ) row174_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row174_coefficients,Fin.sum_univ_succ]
 ring
theorem row174_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row174_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row174_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row174_pos
