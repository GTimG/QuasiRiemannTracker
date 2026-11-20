/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row160_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14543243116429961049719328406693586438041/2614191713825811825730500000000000:ℝ),(168037709750976729946509783443996532963871/13070958569129059128652500000000000:ℝ),(594625433572810867559916180635575563402769/65354792845645295643262500000000000:ℝ),(5618991530690533995507268116143976049259/3112132992649775983012500000000000:ℝ)],
![(375535682333344100589473695956320438200441/32677396422822647821631250000000000:ℝ),(868548376301365056967594589829271518968363/32677396422822647821631250000000000:ℝ),(615604883017053465332779541154052925366203/32677396422822647821631250000000000:ℝ),(5836788460983231553899601365331635457061/1556066496324887991506250000000000:ℝ)],
![(413028755800332096471048955742171139752761/65354792845645295643262500000000000:ℝ),(973068120686029318785681851353164098055083/65354792845645295643262500000000000:ℝ),(712291816088304033207478478675701301341483/65354792845645295643262500000000000:ℝ),(7249157926942954544457017088105159192341/3112132992649775983012500000000000:ℝ)]]
theorem row160_identity (δ p : ℝ) : rowMargin .newTop .C δ p =
 Record12518109.Bernstein.bsum 2 3 (5618991530690533995507268116143976049259/47525366841718742146719783321600000000000000:ℝ) row160_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row160_coefficients,Fin.sum_univ_succ]
 ring
theorem row160_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .C δ p := by
 rw [row160_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row160_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row160_pos
