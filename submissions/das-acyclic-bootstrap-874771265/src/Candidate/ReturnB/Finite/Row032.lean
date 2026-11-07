/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row032_coefficients : Fin 3 → Fin 4 → ℝ := ![![(57272703255074250367793627580266161/25903341910957136484375000:ℝ),(170099204484673898871702792791690257/25903341910957136484375000:ℝ),(21048440906661428405015316599781632/3237917738869642060546875:ℝ),(1389025428634130115040994213108224/647583547773928412109375:ℝ)],
![(27580685633661939799489899245112989/6475835477739284121093750:ℝ),(16378323030581107231127524555011097/1295167095547856824218750:ℝ),(1227951612648674809604990251179008/98118719359686123046875:ℝ),(405058672244445132063193412657152/98118719359686123046875:ℝ)],
![(241307772748082242620125258979631/117742463231623347656250:ℝ),(39395075499695803198261763644544377/6475835477739284121093750:ℝ),(19488096951118735642164504043896832/3237917738869642060546875:ℝ),(6426521787255939500528186062314496/3237917738869642060546875:ℝ)]]
theorem row032_identity (δ p : ℝ) : rowMargin .oldSmall .P δ p =
 Record12518109.Bernstein.bsum 2 3 (6275900182867128418484556701479/48287329151331182837760000000000:ℝ) row032_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row032_coefficients,Fin.sum_univ_succ]
 ring
theorem row032_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .P δ p := by
 rw [row032_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row032_pos
