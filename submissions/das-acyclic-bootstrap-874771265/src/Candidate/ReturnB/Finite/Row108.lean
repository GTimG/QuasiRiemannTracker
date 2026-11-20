/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def row108_coefficients : Fin 3 → Fin 4 → ℝ := ![![(174671517797600531663352933293/839468076248201830031250000:ℝ),(2137414330436935075988779580723/4197340381241009150156250000:ℝ),(1725152612319303554085375294751/4197340381241009150156250000:ℝ),(152942915088684117293620126831/1399113460413669716718750000:ℝ)],
![(166628933884583582416608679637/419734038124100915015625000:ℝ),(367939208633775277482173458231/419734038124100915015625000:ℝ),(256239426646381595030307361061/419734038124100915015625000:ℝ),(18083004738631421534997527489/139911346041366971671875000:ℝ)],
![(27333845089447650221549402971/76315279658927439093750000:ℝ),(3519975682224758329833677122187/4197340381241009150156250000:ℝ),(1337595736879069042233876104117/2098670190620504575078125000:ℝ),(54456353236940270968430604121/349778365103417429179687500:ℝ)]]
theorem row108_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (18083004738631421534997527489/4075213321852011491328000000000:ℝ) row108_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row108_coefficients,Fin.sum_univ_succ]
 ring
theorem row108_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp : p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row108_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row108_coefficients]
end
end DasStageBFinite
#print axioms DasStageBFinite.row108_pos
