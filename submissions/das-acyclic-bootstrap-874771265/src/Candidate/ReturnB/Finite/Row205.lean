/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row205_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1396545838215214336885557159975652280822/2417012448450378685524052734375:ℝ),(1215374153666012253217962375761816624974/805670816150126228508017578125:ℝ),(345356495753791252361267033686694382592/268556938716708742836005859375:ℝ),(858620953499690541907973693431897161728/2417012448450378685524052734375:ℝ)],
![(60857121146951428185478464401667448984/53711387743341748567201171875:ℝ),(7120693524208334126242873202489370489544/2417012448450378685524052734375:ℝ),(6036948269027211742444526233570948968448/2417012448450378685524052734375:ℝ),(551601094378112200241266778409339977728/805670816150126228508017578125:ℝ)],
![(1349397813192696316660252942934914826008/2417012448450378685524052734375:ℝ),(3496624675578261236074573178023153415272/2417012448450378685524052734375:ℝ),(590145530778069590989471653407255588864/483402489690075737104810546875:ℝ),(803489763244022533216191386637570605056/2417012448450378685524052734375:ℝ)]]
theorem row205_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (12260280811218605548342764078332071/72090204306383766202369966080000000000:ℝ) row205_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row205_coefficients,Fin.sum_univ_succ]
 ring
theorem row205_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row205_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row205_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row205_pos
