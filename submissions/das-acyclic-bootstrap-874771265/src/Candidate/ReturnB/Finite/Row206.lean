/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row206_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15358553226186027208960109288955183956/89518979572236247612001953125:ℝ),(40863202887762358604522299475176399124/89518979572236247612001953125:ℝ),(192799270278329629130162597637137222542/483402489690075737104810546875:ℝ),(275368053463897072391422191830096115674/2417012448450378685524052734375:ℝ)],
![(271189945494870723987699542382310441432/805670816150126228508017578125:ℝ),(718368623351667648800200980521741005736/805670816150126228508017578125:ℝ),(60399687536352813331303689128299593488/77968143498399312436259765625:ℝ),(530848694314083327269831877557589455216/2417012448450378685524052734375:ℝ)],
![(135442769317214511360388944067391460028/805670816150126228508017578125:ℝ),(71603412453465192818782549275366019204/161134163230025245701603515625:ℝ),(103397727626433723258854388998395544452/268556938716708742836005859375:ℝ),(87617946881760880025896296854341747364/805670816150126228508017578125:ℝ)]]
theorem row206_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (21904486720440220006474074213585436841/98427158946315968788302460354560000000000:ℝ) row206_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row206_coefficients,Fin.sum_univ_succ]
 ring
theorem row206_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row206_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row206_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row206_pos
