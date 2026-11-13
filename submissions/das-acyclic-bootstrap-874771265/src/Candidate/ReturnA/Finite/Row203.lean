/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row203_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1556626238659552272023331113030362154859236/362554294719123619498601455078125:ℝ),(4348519268807964495022808273580881095317676/362554294719123619498601455078125:ℝ),(4028819076020497707178215502069053836227244/362554294719123619498601455078125:ℝ),(15270672028656501024372642284373887602084/4475978947149674314797548828125:ℝ)],
![(3030129900185259728530820393818369146964936/362554294719123619498601455078125:ℝ),(8442957312478661971453290518046229811196248/362554294719123619498601455078125:ℝ),(7798864440476794489646555081717990990390488/362554294719123619498601455078125:ℝ),(29457207208357496567045751518382010199496/4475978947149674314797548828125:ℝ)],
![(59294063396247715256086613397007250032292/14502171788764944779944058203125:ℝ),(588706031621347635722876165546274216510196/51793470674160517071228779296875:ℝ),(3796510016061533116906829117874862061903444/362554294719123619498601455078125:ℝ),(2042182974943587997042762191590434110916/639425563878524902113935546875:ℝ)]]
theorem row203_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (4594911693623072993346214931078476749561/22497786962613234657697418769858560000000000:ℝ) row203_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (255/512:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row203_coefficients,Fin.sum_univ_succ]
 ring
theorem row203_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row203_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row203_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row203_pos
