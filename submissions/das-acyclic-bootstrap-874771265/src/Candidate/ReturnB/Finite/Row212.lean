/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row212_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5381831013688492852498149346627111340384/2417012448450378685524052734375:ℝ),(13805079658044601406435243731524591686816/2417012448450378685524052734375:ℝ),(2297700390810494547964509080715587731456/483402489690075737104810546875:ℝ),(3065206875305805039345096885853583310848/2417012448450378685524052734375:ℝ)],
![(2160416714728736919626543189242464403408/483402489690075737104810546875:ℝ),(9236042922624333805484142471756926955344/805670816150126228508017578125:ℝ),(2561980392440892617179248532720927318016/268556938716708742836005859375:ℝ),(6151685175069050600513194565264574513152/2417012448450378685524052734375:ℝ)],
![(1809208586583429376944615268140247526402/805670816150126228508017578125:ℝ),(13925102722196363879502770786565421979866/2417012448450378685524052734375:ℝ),(173004618277056989530521294441134113792/36074812663438487843642578125:ℝ),(1031261911124207345189487474750813011968/805670816150126228508017578125:ℝ)]]
theorem row212_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (11692836285804004819279086631216367/72090204306383766202369966080000000000:ℝ) row212_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row212_coefficients,Fin.sum_univ_succ]
 ring
theorem row212_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row212_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row212_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row212_pos
