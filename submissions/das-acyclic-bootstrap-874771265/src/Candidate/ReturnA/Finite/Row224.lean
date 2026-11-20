/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row224_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43160596637373670911486546194459/1021860507819080104098281250000:ℝ),(5859855365996978946909962256689999/82770701133345488431960781250000:ℝ),(1322279249083050547053492057236393/41385350566672744215980390625000:ℝ),(90134268055705683917980737266983/41385350566672744215980390625000:ℝ)],
![(897821251147203066753765359541019/6897558427778790702663398437500:ℝ),(4921380054914187036990179304782983/20692675283336372107990195312500:ℝ),(537448112274822360396491194756219/4138535056667274421598039062500:ℝ),(392362310778215216459258997621169/20692675283336372107990195312500:ℝ)],
![(1500867018573390712477563171066779/13795116855557581405326796875000:ℝ),(9115922849451714501258285196406179/41385350566672744215980390625000:ℝ),(5934480208683135483178205385572747/41385350566672744215980390625000:ℝ),(246375163224100290858704940473381/8277070113334548843196078125000:ℝ)]]
theorem row224_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (90134268055705683917980737266983/75339731520485137914958080000000000:ℝ) row224_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row224_coefficients,Fin.sum_univ_succ]
 ring
theorem row224_pos {δ p : ℝ} (hd : δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row224_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row224_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row224_pos
