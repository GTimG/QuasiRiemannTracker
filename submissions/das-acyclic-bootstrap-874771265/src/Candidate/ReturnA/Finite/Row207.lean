/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row207_coefficients : Fin 3 → Fin 4 → ℝ := ![![(68487664939849639570264718201830525863344/120851431573041206499533818359375:ℝ),(106730556667077417758761736638347593690768/72510858943824723899720291015625:ℝ),(451767349490980177710213432490685016694784/362554294719123619498601455078125:ℝ),(123575906735990540306942231045173000830976/362554294719123619498601455078125:ℝ)],
![(44995514354178883103271789694363987687408/40283810524347068833177939453125:ℝ),(209637703883931413009122675869657087944176/72510858943824723899720291015625:ℝ),(883210322267030455502902560178664300191744/362554294719123619498601455078125:ℝ),(239978102073055060014790037518795374657536/362554294719123619498601455078125:ℝ)],
![(13373508319374780488699097294062072928956/24170286314608241299906763671875:ℝ),(14795537406750626723534682984135709262204/10358694134832103414245755859375:ℝ),(86948236201396498506522391984619336906752/72510858943824723899720291015625:ℝ),(23499664153760684630181114772054809608192/72510858943824723899720291015625:ℝ)]]
theorem row207_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (717152836723653705755038902955774219/4325441219008281809799003242496000000000:ℝ) row207_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row207_coefficients,Fin.sum_univ_succ]
 ring
theorem row207_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row207_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row207_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row207_pos
