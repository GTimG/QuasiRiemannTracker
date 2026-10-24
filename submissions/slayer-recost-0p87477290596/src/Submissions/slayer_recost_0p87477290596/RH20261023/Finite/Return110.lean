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
def row110_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1168945110895878890282324/81016685132958984375:ℝ),(1887507410387811781418324/48610011079775390625:ℝ),(8460492372297500007296636/243050055398876953125:ℝ),(2529790653046077771051988/243050055398876953125:ℝ)],
  ![(2006431661293503390821002/81016685132958984375:ℝ),(15650403070680828794314094/243050055398876953125:ℝ),(13474351451753768252482552/243050055398876953125:ℝ),(3843243364953449630631464/243050055398876953125:ℝ)],
  ![(7454417984302833522210427/648133481063671875000:ℝ),(56292538841157847404727889/1944400443191015625000:ℝ),(5813213122969969394812808/243050055398876953125:ℝ),(1572052511938801040050732/243050055398876953125:ℝ)]
]
theorem row110_identity (δ p : ℝ) : rowMargin .newSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (393013127984700260012683/113269535506636800000000000:ℝ) row110_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row110_coefficients,Fin.sum_univ_succ] <;> ring
theorem row110_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capC δ p := by
 rw [row110_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row110_coefficients]
#print axioms row110_identity
#print axioms row110_pos
end
end RH20261023Finite
