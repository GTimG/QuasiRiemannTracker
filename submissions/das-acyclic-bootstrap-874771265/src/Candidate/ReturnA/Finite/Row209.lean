/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row209_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2956938236505046300217478423315082071344/362554294719123619498601455078125:ℝ),(7456899162277378397357678048063510489896/362554294719123619498601455078125:ℝ),(173449041047263974235781508615430536046/10358694134832103414245755859375:ℝ),(74792829430655463950930104092570671098/17264490224720172357076259765625:ℝ)],
![(5986619810807512574981195841242315056528/362554294719123619498601455078125:ℝ),(15049355761811442672047314164640303827248/362554294719123619498601455078125:ℝ),(12195688368802485793008533580130798240912/362554294719123619498601455078125:ℝ),(149177847212566900476611130335490927152/17264490224720172357076259765625:ℝ)],
![(453097107121757706759614564852325488312/51793470674160517071228779296875:ℝ),(8015926334521857305704955321136313078552/362554294719123619498601455078125:ℝ),(6545933786663621720486668533014856902552/362554294719123619498601455078125:ℝ),(81027409464072833215128157599753440104/17264490224720172357076259765625:ℝ)]]
theorem row209_identity (δ p : ℝ) : rowMargin .newKink .C δ p =
 Record12518109.Bernstein.bsum 2 3 (9323615450785431279788195645968182947/32955742621015480455611453276160000000000:ℝ) row209_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row209_coefficients,Fin.sum_univ_succ]
 ring
theorem row209_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .C δ p := by
 rw [row209_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row209_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row209_pos
