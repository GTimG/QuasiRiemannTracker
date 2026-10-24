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
def row078_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(131995041991646965360623352/16203337026591796875:ℝ),(5642764432750087482131885704/243050055398876953125:ℝ),(214153403566296720777089792/9722002215955078125:ℝ),(1690996286282035017704709376/243050055398876953125:ℝ)],
  ![(253145191013107308083853644/16203337026591796875:ℝ),(10780863988631019322910431604/243050055398876953125:ℝ),(10186699280683062764126365696/243050055398876953125:ℝ),(3203013157248653062473738752/243050055398876953125:ℝ)],
  ![(244557688988867548166951831/32406674053183593750:ℝ),(10377015273348533728027922009/486100110797753906250:ℝ),(4882892227426389765081012032/243050055398876953125:ℝ),(305713451633725902463837952/48610011079775390625:ℝ)]
]
theorem row078_identity (δ p : ℝ) : rowMargin .oldSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1194193170444241806499367/362462513621237760000000000:ℝ) row078_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row078_coefficients,Fin.sum_univ_succ] <;> ring
theorem row078_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capC δ p := by
 rw [row078_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_coefficients]
#print axioms row078_identity
#print axioms row078_pos
end
end RH20261023Finite
