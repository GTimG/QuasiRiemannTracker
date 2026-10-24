/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row160_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7271353317532173434880838649351543517077/1307079066911496586875000000000000:ℝ),(3360608925102591328118348740560513134651/261415813382299317375000000000000:ℝ),(11891859408747849653191901665219586215877/1307079066911496586875000000000000:ℝ),(786595097154656002279533219815590103233/435693022303832195625000000000000:ℝ)],
![(7510439711670601989844564129125538110461/653539533455748293437500000000000:ℝ),(17370226423826802476160832560880147014583/653539533455748293437500000000000:ℝ),(12311435947183906172342785909210331220743/653539533455748293437500000000000:ℝ),(817085536700483625037079517332490772207/217846511151916097812500000000000:ℝ)],
![(8260287631169517683436647964754190035901/1307079066911496586875000000000000:ℝ),(19460583106442422271073889788495261781303/1307079066911496586875000000000000:ℝ),(3230922844005378262628914833462221167/296457034908481875000000000000:ℝ),(1014813550571583985323426892174620459967/435693022303832195625000000000000:ℝ)]]
theorem row160_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (786595097154656002279533219815590103233/6653465891165716820199997440000000000000000:ℝ) row160_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row160_coefficients,Fin.sum_univ_succ]
 ring
theorem row160_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row160_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row160_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row160_pos
