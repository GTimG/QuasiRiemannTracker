/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row143_coefficients : Fin 3 → Fin 4 → ℝ := ![![(463926409113187086124456541567715899/3730104776754476185050000000000000:ℝ),(1031044997453392817786174849017388449/3730104776754476185050000000000000:ℝ),(730947196946277581440607709771523877/3730104776754476185050000000000000:ℝ),(53938378308531767951355660290617109/1243368258918158728350000000000000:ℝ)],
![(529512290937731233204362352789224179/1865052388377238092525000000000000:ℝ),(212490102590047361836384583953220573/373010477675447618505000000000000:ℝ),(624286205683384052102908335007151987/1865052388377238092525000000000000:ℝ),(29442591050054552412704711951757767/621684129459079364175000000000000:ℝ)],
![(1217312901269053527446694262944781439/3730104776754476185050000000000000:ℝ),(2820420672221283165984814774819489609/3730104776754476185050000000000000:ℝ),(1058118416160424220071166620171364131/1865052388377238092525000000000000:ℝ),(42383228798962214439446856683793341/310842064729539682087500000000000:ℝ)]]
theorem row143_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (29442591050054552412704711951757767/18107862714768988982476800000000000000:ℝ) row143_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row143_coefficients,Fin.sum_univ_succ]
 ring
theorem row143_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row143_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row143_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row143_pos
