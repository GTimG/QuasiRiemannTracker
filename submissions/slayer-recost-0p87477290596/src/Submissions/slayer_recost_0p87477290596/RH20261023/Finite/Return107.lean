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
def row107_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(763464932458187363323720552037249/54653145333345661585876171875000:ℝ),(205811451617979860619531405031117/6831643166668207698234521484375:ℝ),(4557161085089064191726052922117933/218612581333382646343504687500000:ℝ),(199107186593696264230787283854237/43722516266676529268700937500000:ℝ)],
  ![(1127097925450312069479037088336921/27326572666672830792938085937500:ℝ),(2226187659883692600977383617152453/27326572666672830792938085937500:ℝ),(1330317786961605187026164607048667/27326572666672830792938085937500:ℝ),(43293767487847252701364240646627/5465314533334566158587617187500:ℝ)],
  ![(3239631569109497946382391124636593/54653145333345661585876171875000:ℝ),(7358931440219479233461575597371863/54653145333345661585876171875000:ℝ),(548910577625448792984932274727861/5465314533334566158587617187500:ℝ),(67014373748326492936407226227167/2732657266667283079293808593750:ℝ)]
]
theorem row107_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (43293767487847252701364240646627/4974650739675196219016640000000000:ℝ) row107_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row107_coefficients,Fin.sum_univ_succ] <;> ring
theorem row107_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row107_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row107_coefficients]
#print axioms row107_identity
#print axioms row107_pos
end
end RH20261023Finite
