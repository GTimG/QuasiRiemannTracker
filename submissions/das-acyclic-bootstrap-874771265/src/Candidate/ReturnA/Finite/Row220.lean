/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row220_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3581048445978995036052640845101788750367/376918599656853979822698134765625:ℝ),(9071715044744519860969584991221107007637/376918599656853979822698134765625:ℝ),(7431996204136578521041402615819243623023/376918599656853979822698134765625:ℝ),(647070784069352517174568364409089705251/125639533218951326607566044921875:ℝ)],
![(7850328496996524693102943440790585146574/376918599656853979822698134765625:ℝ),(4022067393224918908845019503862889165506/75383719931370795964539626953125:ℝ),(16734593285314557100661532914150841406738/376918599656853979822698134765625:ℝ),(1491448196731335781176026411682951908594/125639533218951326607566044921875:ℝ)],
![(4419056038655339324206304575161279329207/376918599656853979822698134765625:ℝ),(11485330484280064696917318001923733561093/376918599656853979822698134765625:ℝ),(1949340704855944248453830466287504416393/75383719931370795964539626953125:ℝ),(893435345357827257119076451053147616693/125639533218951326607566044921875:ℝ)]]
theorem row220_identity (δ p : ℝ) : rowMargin .newKink .P δ p =
 Record12518109.Bernstein.bsum 2 3 (647070784069352517174568364409089705251/1918640662258138862916660583464960000000000:ℝ) row220_coefficients (123/256:ℝ) (63/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row220_coefficients,Fin.sum_univ_succ]
 ring
theorem row220_pos {δ p : ℝ} (hd : δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .P δ p := by
 rw [row220_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row220_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row220_pos
