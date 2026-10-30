/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row201_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3024052063101557854242266306031311911523/362554294719123619498601455078125:ℝ),(1105484060934395302727623743996821906671/51793470674160517071228779296875:ℝ),(257239990488315523821253584111261657209/14502171788764944779944058203125:ℝ),(81741079849374881209314043836641666431/17264490224720172357076259765625:ℝ)],
![(5836851112900860337923602534596683870886/362554294719123619498601455078125:ℝ),(590615792814505362139522083013990002338/14502171788764944779944058203125:ℝ),(12074331310879033736105531673765488731642/362554294719123619498601455078125:ℝ),(149789564685682941614484747109966549718/17264490224720172357076259765625:ℝ)],
![(2954797225349140156234920764604417392363/362554294719123619498601455078125:ℝ),(7450476128809659965410005071931516452953/362554294719123619498601455078125:ℝ),(866327629026645809472097117915439246381/51793470674160517071228779296875:ℝ),(74690876518469457094617834630158067337/17264490224720172357076259765625:ℝ)]]
theorem row201_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (74690876518469457094617834630158067337/263645940968123843644891626209280000000000:ℝ) row201_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row201_coefficients,Fin.sum_univ_succ]
 ring
theorem row201_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row201_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row201_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row201_pos
