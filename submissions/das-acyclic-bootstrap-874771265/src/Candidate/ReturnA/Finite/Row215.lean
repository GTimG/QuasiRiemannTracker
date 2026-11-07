/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row215_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17702594100537118559944248501068063/8277070113334548843196078125000:ℝ),(39187559484740112509790324065845589/8277070113334548843196078125000:ℝ),(26715239616228240038358995373818239/8277070113334548843196078125000:ℝ),(5202373419890529943181955746540713/8277070113334548843196078125000:ℝ)],
![(118287936104320243340401878429461539/20692675283336372107990195312500:ℝ),(270013163976661438143080418554018809/20692675283336372107990195312500:ℝ),(193713589697195185184092094685134501/20692675283336372107990195312500:ℝ),(41820956952045693509427770185577231/20692675283336372107990195312500:ℝ)],
![(191953557169236145410026379406810963/41385350566672744215980390625000:ℝ),(470560541568680869983788542669482073/41385350566672744215980390625000:ℝ),(375358078537865128113426622229301857/41385350566672744215980390625000:ℝ),(96550208291050447293281517716630747/41385350566672744215980390625000:ℝ)]]
theorem row215_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5202373419890529943181955746540713/3857394253848839061245853696000000000:ℝ) row215_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row215_coefficients,Fin.sum_univ_succ]
 ring
theorem row215_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row215_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row215_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row215_pos
