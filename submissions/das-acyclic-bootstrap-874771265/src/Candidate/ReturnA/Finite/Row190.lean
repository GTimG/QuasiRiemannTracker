/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def row190_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1154485553979029176530087423802697/331082804533381953727843125000000:ℝ),(3095451229635873357110670525811451/331082804533381953727843125000000:ℝ),(2727445797334659184631078780214811/331082804533381953727843125000000:ℝ),(786480121677815004050495678206057/331082804533381953727843125000000:ℝ)],
![(180769632389050929135320938284209/165541402266690976863921562500000:ℝ),(6466455007840989472110980517433/2331569046009732068505937500000:ℝ),(410014622277064035766212320249359/165541402266690976863921562500000:ℝ),(5266637964376188495266145671833/6621656090667639074556862500000:ℝ)],
![(531384928932600496651926952765721/331082804533381953727843125000000:ℝ),(143578023950469432334507984118347/66216560906676390745568625000000:ℝ),(245283729396063623555954517603157/331082804533381953727843125000000:ℝ),(14137239160771126005799049777143/331082804533381953727843125000000:ℝ)]]
theorem row190_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (14137239160771126005799049777143/18834932880121284478739520000000000:ℝ) row190_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row190_coefficients,Fin.sum_univ_succ]
 ring
theorem row190_pos {δ p : ℝ} (hd : δ∈Set.Icc (0/1:ℝ) (3/8:ℝ)) (hp : p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row190_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row190_coefficients]
end
end DasStageAFinite
#print axioms DasStageAFinite.row190_pos
