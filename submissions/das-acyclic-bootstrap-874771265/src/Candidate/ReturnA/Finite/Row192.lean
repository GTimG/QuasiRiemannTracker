/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row192_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1076703325238433035912692908086371/8277070113334548843196078125000:ℝ),(12101850959232952238580455397386941/41385350566672744215980390625000:ℝ),(8726544695021113021215200742912017/41385350566672744215980390625000:ℝ),(661963237424184348644479545318977/13795116855557581405326796875000:ℝ)],
![(1207554328402254027145954477554619/4138535056667274421598039062500:ℝ),(2447336256027416064807815802681977/4138535056667274421598039062500:ℝ),(1467209941721422009374690063204907/4138535056667274421598039062500:ℝ),(73577273061309365611132454359183/1379511685555758140532679687500:ℝ)],
![(2720289671807014872499700009950567/8277070113334548843196078125000:ℝ),(31548005843335576918332963212131429/41385350566672744215980390625000:ℝ),(11852269679309937990474358300675339/20692675283336372107990195312500:ℝ),(475646701039740363626543177206007/3448779213889395351331699218750:ℝ)]]
theorem row192_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (73577273061309365611132454359183/40181190144258740221310976000000000:ℝ) row192_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row192_coefficients,Fin.sum_univ_succ]
 ring
theorem row192_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row192_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row192_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row192_pos
