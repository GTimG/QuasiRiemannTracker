/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row202_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64752110230647352607529756271468717888222/362554294719123619498601455078125:ℝ),(173755342984785728553076391357236290543514/362554294719123619498601455078125:ℝ),(153462970738714266837303288013051191193562/362554294719123619498601455078125:ℝ),(8891867019369733118123614761244223707654/72510858943824723899720291015625:ℝ)],
![(24980701707380850684973470022732599328012/72510858943824723899720291015625:ℝ),(333108828018108363689945232037118358003764/362554294719123619498601455078125:ℝ),(4111685140588721158746285901819988038988/5106398517170755204205654296875:ℝ),(83723509122832030211496033097295039404444/362554294719123619498601455078125:ℝ)],
![(61267320108860015461164711910142253672238/362554294719123619498601455078125:ℝ),(6507651429079006037246756838718057796362/14502171788764944779944058203125:ℝ),(141794543626447045032780843330846300690686/362554294719123619498601455078125:ℝ),(40370164448544042732712466058220703203874/362554294719123619498601455078125:ℝ)]]
theorem row202_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (20185082224272021366356233029110351601937/88585036165289611464683586406318080000000000:ℝ) row202_coefficients (57/128:ℝ) (231/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row202_coefficients,Fin.sum_univ_succ]
 ring
theorem row202_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row202_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row202_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row202_pos
