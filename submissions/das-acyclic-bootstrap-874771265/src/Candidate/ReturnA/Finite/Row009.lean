/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![![(819205210512516691718564239/237159944296875000:ℝ),(488789299570386605887109539/47431988859375000:ℝ),(4860595267234497557529181601/474319888593750000:ℝ),(537037564185221627365071563/158106629531250000:ℝ)],
![(792002169159959176989579829/118579972148437500:ℝ),(2362386636806835517815544187/118579972148437500:ℝ),(587196850869522681507044968/29644993037109375:ℝ),(129733822638535730867035919/19763328691406250:ℝ)],
![(765226143902076535359245449/237159944296875000:ℝ),(2282111015396996659230150179/237159944296875000:ℝ),(2268564609405526188956478601/237159944296875000:ℝ),(250559912636868688361857957/79053314765625000:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (250559912636868688361857957/1207222761097789440000000000:ℝ) row009_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ]
 ring
theorem row009_pos {δ p : ℝ} (hd : δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row009_pos
