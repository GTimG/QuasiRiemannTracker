/- Generated 2026-10-23 by exact rational Bernstein conversion.
Candidate c=3130677351/25000000000, h=400051/500000.
Compilation status is recorded separately; no new axioms are introduced.
Original mathematical/formal interface: Hailey Collet and Mark Lewko.
Original source released under Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def row109_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(104989843595735095814379692310903013/27326572666672830792938085937500:ℝ),(278667449881143473156386097661318799/27326572666672830792938085937500:ℝ),(245677164456967306419806860386516023/27326572666672830792938085937500:ℝ),(71940521311202975509716467536100237/27326572666672830792938085937500:ℝ)],
  ![(85485820714863326005600810118140957/13663286333336415396469042968750:ℝ),(8558647786368212950532316615753943/546531453333456615858761718750:ℝ),(175501331990392572607755888532751069/13663286333336415396469042968750:ℝ),(46947161970605632889943798882043451/13663286333336415396469042968750:ℝ)],
  ![(95656639582006124273482761744227839/27326572666672830792938085937500:ℝ),(234942539136574858042512897154347667/27326572666672830792938085937500:ℝ),(375612982256229553424574514910071759/54653145333345661585876171875000:ℝ),(96856692958479730986251783152332103/54653145333345661585876171875000:ℝ)]
]
theorem row109_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (46947161970605632889943798882043451/12735105893568502320682598400000000000:ℝ) row109_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row109_coefficients,Fin.sum_univ_succ] <;> ring
theorem row109_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row109_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row109_coefficients]
#print axioms row109_identity
#print axioms row109_pos
end
end RH20261023Finite
