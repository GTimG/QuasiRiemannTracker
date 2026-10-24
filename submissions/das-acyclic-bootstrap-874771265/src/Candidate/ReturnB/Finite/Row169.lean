/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row169_coefficients : Fin 3 → Fin 4 → ℝ := ![![(243716713084204681117195976990921115218312243/1021155521024606708496093750000:ℝ),(304737346874767541470589270177712785895347219/638222200640379192810058593750:ℝ),(76278017456533927789732478768391350279192576/319111100320189596405029296875:ℝ),(70815319356341924531795767959772266758144/319111100320189596405029296875:ℝ)],
![(194913518495733442275909617569636360479012313/408462208409842683398437500000:ℝ),(243648734495667125446802677212241815070506361/255288880256151677124023437500:ℝ),(30468693027667503697671942066972118431408128/63822220064037919281005859375:ℝ),(11746053142971269915955260582505219620864/63822220064037919281005859375:ℝ)],
![(779737708291961692531443978432464131580357239/3267697667278741467187500000000:ℝ),(194927202662932618371463047423289424147590187/408462208409842683398437500000:ℝ),(3046402848437606714559489228426906105617408/12764444012807583856201171875:ℝ),(778126667526128891844195091269777883136/12764444012807583856201171875:ℝ)]]
theorem row169_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (2968317670921817366959362378195869/3193663627759544073695998771200000000000000:ℝ) row169_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row169_coefficients,Fin.sum_univ_succ]
 ring
theorem row169_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row169_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row169_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row169_pos
