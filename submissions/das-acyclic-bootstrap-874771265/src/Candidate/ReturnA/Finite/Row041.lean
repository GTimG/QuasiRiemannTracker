/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row041_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5111552521048179917447205262019/3333027506897591279296875:ℝ),(14921694737397359133382685631781/3333027506897591279296875:ℝ),(5805721279462301317417764987857/1333211002759036511718750:ℝ),(3136088769240905793545772441587/2222018337931727519531250:ℝ)],
![(9152895896725163612922086029034/3333027506897591279296875:ℝ),(8882723280374871217915061142842/1111009168965863759765625:ℝ),(1033976585959214928764821986268/133321100275903651171875:ℝ),(2784692954530518550328577835736/1111009168965863759765625:ℝ)],
![(272437096607411821608936505351/222201833793172751953125:ℝ),(2372302441532576188132687109359/666605501379518255859375:ℝ),(2293909310934346795670412289309/666605501379518255859375:ℝ),(246303762667655078665521982001/222201833793172751953125:ℝ)]]
theorem row041_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (246303762667655078665521982001/3313713921017029853184000000000:ℝ) row041_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row041_coefficients,Fin.sum_univ_succ]
 ring
theorem row041_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row041_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row041_pos
