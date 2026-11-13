/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row221_coefficients : Fin 3 → Fin 4 → ℝ := ![![(545954141199598164066055585980020364842/75383719931370795964539626953125:ℝ),(92689478457486853443951358500885481646/5308712671223295490460537109375:ℝ),(5003953516064696201508154156689860029952/376918599656853979822698134765625:ℝ),(1152653998418124282717132256554436407296/376918599656853979822698134765625:ℝ)],
![(6051461297773873881141224908394521142696/376918599656853979822698134765625:ℝ),(14842824378589086573346379516179289198696/376918599656853979822698134765625:ℝ),(11595449029934053876755353703334345160704/376918599656853979822698134765625:ℝ),(2803845723126361278538899494971452104704/376918599656853979822698134765625:ℝ)],
![(3468864389863415040163802189832275558536/376918599656853979822698134765625:ℝ),(1740161550706193838458788459507526628776/75383719931370795964539626953125:ℝ),(7027863881412760790547179424105457559552/376918599656853979822698134765625:ℝ),(1795797475163692540216129764884474974208/376918599656853979822698134765625:ℝ)]]
theorem row221_identity (δ p : ℝ) : rowMargin .newKink .P δ p =
 Record12518109.Bernstein.bsum 2 3 (281409667582549873710237367322860451/1405254391302347799987788513280000000000:ℝ) row221_coefficients (123/256:ℝ) (63/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row221_coefficients,Fin.sum_univ_succ]
 ring
theorem row221_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .P δ p := by
 rw [row221_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row221_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row221_pos
