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
def row112_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2176280642962920420292986583/972200221595507812500:ℝ),(6215570269598900298999746149/972200221595507812500:ℝ),(5910404967553676336012056781/972200221595507812500:ℝ),(374223068183539291461059443/194440044319101562500:ℝ)],
  ![(2030607286954072217698610791/486100110797753906250:ℝ),(5761228228849181044954230661/486100110797753906250:ℝ),(1087815922036591337250004237/97220022159550781250:ℝ),(341691733657569571798880263/97220022159550781250:ℝ)],
  ![(1954276231659765851609980159/972200221595507812500:ℝ),(1102671031545111593009297393/194440044319101562500:ℝ),(5172677898755475591359749631/972200221595507812500:ℝ),(64543958907587339116929713/38888008863820312500:ℝ)]
]
theorem row112_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (64543958907587339116929713/18558080697407373312000000000:ℝ) row112_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row112_coefficients,Fin.sum_univ_succ] <;> ring
theorem row112_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row112_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row112_coefficients]
#print axioms row112_identity
#print axioms row112_pos
end
end RH20261023Finite
