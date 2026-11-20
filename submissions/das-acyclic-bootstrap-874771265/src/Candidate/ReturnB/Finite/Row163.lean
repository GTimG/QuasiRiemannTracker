/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row163_coefficients : Fin 3 → Fin 4 → ℝ := ![![(224174509220880411226209599273812343780453/10211555210246067084960937500000:ℝ),(523239463616523402665043565249701159853103/10211555210246067084960937500000:ℝ),(374346681016314331104571717509883961297239/10211555210246067084960937500000:ℝ),(75281535216019790445416553057834248349589/10211555210246067084960937500000:ℝ)],
![(223661525118175927305793182465432865351073/5105777605123033542480468750000:ℝ),(104226890157396860431926382705405254611047/1021155521024606708496093750000:ℝ),(185838408980725310819741645396884104192287/2552888802561516771240234375000:ℝ),(74203700274514250292181306132692875289787/5105777605123033542480468750000:ℝ)],
![(450257125714420510964824779333228343082131/20423110420492134169921875000000:ℝ),(1049930108954981109653528729523141447489841/20423110420492134169921875000000:ℝ),(2999505009281561346392596855027858947639977/81692441681968536679687500000000:ℝ),(300405767625376618095121317177207846449881/40846220840984268339843750000000:ℝ)]]
theorem row163_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (74203700274514250292181306132692875289787/5109861804415270517913598033920000000000000000:ℝ) row163_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (511/1024:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row163_coefficients,Fin.sum_univ_succ]
 ring
theorem row163_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (511/1024:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row163_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row163_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row163_pos
