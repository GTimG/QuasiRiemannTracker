/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row213_coefficients : Fin 3 → Fin 4 → ℝ := ![![(90228651783262550297683217651654424845476/40283810524347068833177939453125:ℝ),(297500522877886014164517088617458329357228/51793470674160517071228779296875:ℝ),(346486187162458998233395287480568229705728/72510858943824723899720291015625:ℝ),(461978132404679330967685367826331260387328/362554294719123619498601455078125:ℝ)],
![(77718611371516301542239744553095580824304/17264490224720172357076259765625:ℝ),(4186318542524205236513597015761677969009392/362554294719123619498601455078125:ℝ),(3483580866351510047817515245432384049324032/362554294719123619498601455078125:ℝ),(929339099782806882712221699469291402625024/362554294719123619498601455078125:ℝ)],
![(10948519509000534104262935780230188747184/4834057262921648259981352734375:ℝ),(2107122955531005096433886603727672016418896/362554294719123619498601455078125:ℝ),(1754448138770147271390461640264660301832192/362554294719123619498601455078125:ℝ),(468457092809866455187594099029611816452096/362554294719123619498601455078125:ℝ)]]
theorem row213_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (14098453747701395598379070063059425671/86508824380165636195980064849920000000000:ℝ) row213_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row213_coefficients,Fin.sum_univ_succ]
 ring
theorem row213_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row213_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row213_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row213_pos
