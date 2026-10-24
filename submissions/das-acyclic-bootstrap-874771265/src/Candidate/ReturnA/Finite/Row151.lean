/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row151_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3042002258778889961362555237882242439/9325261941886190462625000000000:ℝ),(166527791636936071787991936982585046563/233131548547154761565625000000000:ℝ),(214156398770208437852799794526844466371/466263097094309523131250000000000:ℝ),(6635642787064583262245855902760736539/93252619418861904626250000000000:ℝ)],
![(15655687436383424669585266407934033697/23313154854715476156562500000000:ℝ),(33890907516331495362418425530037347051/23313154854715476156562500000000:ℝ),(21269755180787119851906011187075724537/23313154854715476156562500000000:ℝ),(3032144100843483260787125439500536183/23313154854715476156562500000000:ℝ)],
![(18735061148045851550576679018267211817/46626309709430952313125000000000:ℝ),(42295540265953756466434584052796101211/46626309709430952313125000000000:ℝ),(28862293281555666278419895082526727971/46626309709430952313125000000000:ℝ),(5299297321547165680155962021185338577/46626309709430952313125000000000:ℝ)]]
theorem row151_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3032144100843483260787125439500536183/22250941703908133661667491840000000000000:ℝ) row151_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row151_coefficients,Fin.sum_univ_succ]
 ring
theorem row151_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row151_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row151_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row151_pos
