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
def row114_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(14458228983455344405518011474/243050055398876953125:ℝ),(1684733592569607795053368546/9722002215955078125:ℝ),(40878889009225314893045905319/243050055398876953125:ℝ),(4406259392813488140743234381/81016685132958984375:ℝ)],
  ![(27886392493998636893507805388/243050055398876953125:ℝ),(16215367827594511522619212516/48610011079775390625:ℝ),(78528983377210141476736925824/243050055398876953125:ℝ),(938464323453193361375876616/9001853903662109375:ℝ)],
  ![(13563757464606660922469268734/243050055398876953125:ℝ),(39363748471074282137047721578/243050055398876953125:ℝ),(7610763420979179187776213862/48610011079775390625:ℝ),(4084608699476091574767538822/81016685132958984375:ℝ)]
]
theorem row114_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (2042304349738045787383769411/618602689913579110400000000000:ℝ) row114_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row114_coefficients,Fin.sum_univ_succ] <;> ring
theorem row114_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row114_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row114_coefficients]
#print axioms row114_identity
#print axioms row114_pos
end
end RH20261023Finite
