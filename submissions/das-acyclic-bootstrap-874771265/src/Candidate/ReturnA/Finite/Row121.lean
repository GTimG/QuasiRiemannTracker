/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row121_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7274292554914818453011024093400236273/1532107964309842402998046875:ℝ),(64157545899254425057012117271480905219/4596323892929527208994140625:ℝ),(62857534802336465421156519120426285056/4596323892929527208994140625:ℝ),(20522845836914024902993450390864838656/4596323892929527208994140625:ℝ)],
![(2879649243592021222092031889300008964/306421592861968480599609375:ℝ),(126948543200648601296320957790401416188/4596323892929527208994140625:ℝ),(124335156336463296941299097219451805696/4596323892929527208994140625:ℝ),(40581310056877752455988164752925523968/4596323892929527208994140625:ℝ)],
![(1018401506717762589861583298687726396/218872566329977486142578125:ℝ),(62834585730101937483159838614867651244/4596323892929527208994140625:ℝ),(12304217367549501386909021535819194368/919264778585905441798828125:ℝ),(20072911745928197321690774008545574912/4596323892929527208994140625:ℝ)]]
theorem row121_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
 Record12518109.Bernstein.bsum 2 3 (612576652402593912405113952897509/274181400027162847157944320000000000:ℝ) row121_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row121_coefficients,Fin.sum_univ_succ]
 ring
theorem row121_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
 rw [row121_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row121_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row121_pos
