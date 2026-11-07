/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row207_coefficients : Fin 3 → Fin 4 → ℝ := ![![(152183997190128205178419927943403363416/268556938716708742836005859375:ℝ),(711479832026726765182230480738059949896/483402489690075737104810546875:ℝ),(3011502138445720544783937492703424278528/2417012448450378685524052734375:ℝ),(274582641587493354387239265064428683264/805670816150126228508017578125:ℝ)],
![(2699537124194886058185533690776054989224/2417012448450378685524052734375:ℝ),(465823609814363733181905197395835722664/161134163230025245701603515625:ℝ),(1962503771881641752339355095302818492416/805670816150126228508017578125:ℝ),(51602325576731244904258646078506237952/77968143498399312436259765625:ℝ)],
![(267450869855765719355806708824191324206/483402489690075737104810546875:ℝ),(690401719889957208260602532013293778226/483402489690075737104810546875:ℝ),(579599404769292439197672625970121923584/483402489690075737104810546875:ℝ),(156646320345113000654132995616371032064/483402489690075737104810546875:ℝ)]]
theorem row207_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (9560932638251525918831359595725771/57672163445107012961895972864000000000:ℝ) row207_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row207_coefficients,Fin.sum_univ_succ]
 ring
theorem row207_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row207_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row207_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row207_pos
