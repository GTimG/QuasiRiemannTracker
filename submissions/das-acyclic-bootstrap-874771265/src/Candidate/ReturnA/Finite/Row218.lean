/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row218_coefficients : Fin 3 → Fin 4 → ℝ := ![![(88687875667014726458876135240862704704/10358694134832103414245755859375:ℝ),(1562622806000298348387008731905612363584/72510858943824723899720291015625:ℝ),(1268624296428651231343351374281321128384/72510858943824723899720291015625:ℝ),(15561633307035628345343372276749890368/3452898044944034471415251953125:ℝ)],
![(1312978197117625234354947506710126221824/72510858943824723899720291015625:ℝ),(16608724967235255423232683796688445965696/362554294719123619498601455078125:ℝ),(13582422168811269961398317228712126848032/362554294719123619498601455078125:ℝ),(168493304785935049407078907631514856736/17264490224720172357076259765625:ℝ)],
![(720562702558489683653531467231896375496/72510858943824723899720291015625:ℝ),(9219080672221556712312959341719903888976/362554294719123619498601455078125:ℝ),(1094323220169055547201721158818521232766/51793470674160517071228779296875:ℝ),(97327529932918304369809177604598588946/17264490224720172357076259765625:ℝ)]]
theorem row218_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (243150520422431692895990191824217037/823893565525387011390286331904000000000:ℝ) row218_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row218_coefficients,Fin.sum_univ_succ]
 ring
theorem row218_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row218_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row218_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row218_pos
