/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row217_coefficients : Fin 3 → Fin 4 → ℝ := ![![(240256315210404054914729398811409268/502554893439173299983228515625:ℝ),(64357922100243379467266576974768156/55839432604352588887025390625:ℝ),(442826354806421410252190195768574004/502554893439173299983228515625:ℝ),(103824170032629644946014767432069868/502554893439173299983228515625:ℝ)],
![(2644067268149212365822936652849341496/2512774467195866499916142578125:ℝ),(2144907109557306773908659632854340584/837591489065288833305380859375:ℝ),(4991235966203662345156840825467140516/2512774467195866499916142578125:ℝ),(26670917651553280813133098195910228/55839432604352588887025390625:ℝ)],
![(1572021606595399156000264082290307906/2512774467195866499916142578125:ℝ),(1307280113818069281832018998670178344/837591489065288833305380859375:ℝ),(2103937639219496138397126396458099489/1675182978130577666610761718750:ℝ),(322353061202352289180768748589893843/1005109786878346599966457031250:ℝ)]]
theorem row217_identity (δ p : ℝ) : rowMargin .newKink .P δ p =
 Record12518109.Bernstein.bsum 2 3 (25956042508157411236503691858017467/59957134215722619130676772864000000000:ℝ) row217_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row217_coefficients,Fin.sum_univ_succ]
 ring
theorem row217_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .P δ p := by
 rw [row217_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row217_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row217_pos
