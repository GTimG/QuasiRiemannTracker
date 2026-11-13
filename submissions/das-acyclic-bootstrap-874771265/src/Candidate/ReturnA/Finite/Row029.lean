/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row029_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8593976080940750773263314470068911521/3737449068898884697968750000:ℝ),(25524873082525343957289512897649486563/3737449068898884697968750000:ℝ),(25268880101697621401027248507042238563/3737449068898884697968750000:ℝ),(397046753930252663211711908545793501/177973765185661176093750000:ℝ)],
![(8285115916563665836389570117773443681/1868724534449442348984375000:ℝ),(24600941840216567795028882462374417507/1868724534449442348984375000:ℝ),(24347604034572372754669434854078309971/1868724534449442348984375000:ℝ),(76493112491926718564153761995022249/17797376518566117609375000:ℝ)],
![(7981634365039643688148374255480114841/3737449068898884697968750000:ℝ),(3384735747148547119981113880435662293/533921295556983528281250000:ℝ),(23442471025507896358861277857217311129/3737449068898884697968750000:ℝ),(368140658512326939365620381530847139/177973765185661176093750000:ℝ)]]
theorem row029_identity (δ p : ℝ) : rowMargin .oldSmall .C δ p =
 Record12518109.Bernstein.bsum 2 3 (368140658512326939365620381530847139/2717836448065415535856189440000000000:ℝ) row029_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row029_coefficients,Fin.sum_univ_succ]
 ring
theorem row029_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .C δ p := by
 rw [row029_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row029_pos
