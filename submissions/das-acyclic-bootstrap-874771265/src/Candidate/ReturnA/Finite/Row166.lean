/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row166_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4767705451205513437199814828045623302424899/5105843191066038722129882812500:ℝ),(38181756527443582464835547407427754111668383/20423372764264154888519531250000:ℝ),(171215287471656666775001779756542736146944/182351542538072811504638671875:ℝ),(4073208098123956583510134101574396338176/1276460797766509680532470703125:ℝ)],
![(47617435465670693960750733970538184606155869/25529215955330193610649414062500:ℝ),(380921445008776732221348850997601601869065857/102116863821320774442597656250000:ℝ),(2383556293748021639956664547462879926553088/1276460797766509680532470703125:ℝ),(14546178640647247915645985638954996711424/6382303988832548402662353515625:ℝ)],
![(476367519107310682832221271132152463347153411/510584319106603872212988281250000:ℝ),(3809721956118033935498561371171725865684061791/2042337276426415488851953125000000:ℝ),(29774125159477911122705533213731906578584448/31911519944162742013311767578125:ℝ),(807196919285587385810259136782897127424/1276460797766509680532470703125:ℝ)]]
theorem row166_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (98534780186228928931916398533068497/9980327036760935850811154497536000000000000:ℝ) row166_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row166_coefficients,Fin.sum_univ_succ]
 ring
theorem row166_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row166_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row166_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row166_pos
