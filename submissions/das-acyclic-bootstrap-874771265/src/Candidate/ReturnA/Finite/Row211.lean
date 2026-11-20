/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row211_coefficients : Fin 3 → Fin 4 → ℝ := ![![(247057880246106470215197676166948972335864/362554294719123619498601455078125:ℝ),(130322858812109484816288579405982578637448/72510858943824723899720291015625:ℝ),(562954015375812098342116840776747085381688/362554294719123619498601455078125:ℝ),(158395860271685816841241514446642539530312/362554294719123619498601455078125:ℝ)],
![(99661079654933882515187288858144953088752/72510858943824723899720291015625:ℝ),(1314478480541998850862071656161949869593552/362554294719123619498601455078125:ℝ),(1135849870360710849066167115335867800918624/362554294719123619498601455078125:ℝ),(319673283472369169085016881068752071768832/362554294719123619498601455078125:ℝ)],
![(252363439831166057004565886191723768028296/362554294719123619498601455078125:ℝ),(666201987175103942574928839420106353855112/362554294719123619498601455078125:ℝ),(576223724368260860323148106873799056653036/362554294719123619498601455078125:ℝ),(32476682724648806071121974677851262915244/72510858943824723899720291015625:ℝ)]]
theorem row211_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (19799482533960727105155189305830317441289/88585036165289611464683586406318080000000000:ℝ) row211_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row211_coefficients,Fin.sum_univ_succ]
 ring
theorem row211_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row211_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row211_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row211_pos
