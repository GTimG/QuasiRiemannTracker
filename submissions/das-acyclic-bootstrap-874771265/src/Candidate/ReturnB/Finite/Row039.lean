/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row039_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13817802579593649231092687427587/213313754749607216718750000:ℝ),(13219080055803706407265833035779/71104584916535738906250000:ℝ),(3445612598931195962508839056283/19392159522691565156250000:ℝ),(365513611934574814672194483011/6464053174230521718750000:ℝ)],
![(11435130432057892698696914428451/106656877374803608359375000:ℝ),(3618387825850220901974030335649/11850764152755956484375000:ℝ),(10290492737111984392779064274443/35552292458267869453125000:ℝ),(9740678452510961868380334230939/106656877374803608359375000:ℝ)],
![(1884764495381978929908284476543/42662750949921443343750000:ℝ),(1771875065327834011676796597343/14220916983307147781250000:ℝ),(4987193104360812038133529410679/42662750949921443343750000:ℝ),(1556222464201564960289549095193/42662750949921443343750000:ℝ)]]
theorem row039_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1556222464201564960289549095193/19882282995584367722496000000000:ℝ) row039_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row039_coefficients,Fin.sum_univ_succ]
 ring
theorem row039_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row039_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row039_pos
