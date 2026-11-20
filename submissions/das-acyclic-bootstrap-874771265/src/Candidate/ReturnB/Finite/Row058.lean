/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row058_coefficients : Fin 3 → Fin 4 → ℝ := ![![(58211753476190288960122938337356481999/113255289345417292968750000:ℝ),(28667619891832656969811790221382705020523/18687122741993853339843750000:ℝ),(1782546695789907865350130610487257022752/1167945171374615833740234375:ℝ),(197043047706753221918439197569317226528/389315057124871944580078125:ℝ)],
![(38258556743196096520513866523553408924753/37374245483987706679687500000:ℝ),(1227821680112332350796519350228122892421/401873607354706523437500000:ℝ),(47333527233749455064907563217855312064/15572602284994877783203125:ℝ),(47089505940576678024545211386175911104/46717806854984633349609375:ℝ)],
![(152391278951794612919316952602694489907491/298993963871901653437500000000:ℝ),(18192918761874087907430873190805941851803/11959758554876066137500000000:ℝ),(1767489534510108803106433407324321548896/1167945171374615833740234375:ℝ),(53283247983112138628932576601144268512/106176833761328712158203125:ℝ)]]
theorem row058_identity (δ p : ℝ) : rowMargin .oldPeak .C δ p =
 Record12518109.Bernstein.bsum 2 3 (1665101499472254332154143018785758391/25942814071337841107927040000000000000:ℝ) row058_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row058_coefficients,Fin.sum_univ_succ]
 ring
theorem row058_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .C δ p := by
 rw [row058_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row058_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row058_pos
