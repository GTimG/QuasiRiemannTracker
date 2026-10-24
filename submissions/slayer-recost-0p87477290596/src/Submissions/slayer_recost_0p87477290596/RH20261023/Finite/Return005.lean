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
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1073379557600735579863423/1829945829882812500:ℝ),(16807576144255001665089287/9881707481367187500:ℝ),(81159225370360520080940573/49408537406835937500:ℝ),(26102592704305372411806559/49408537406835937500:ℝ)],
  ![(34636946469673021179083647/32939024937890625000:ℝ),(300204101222935189095793909/98817074813671875000:ℝ),(72198358836526106077590893/24704268703417968750:ℝ),(23125043383047074687955151/24704268703417968750:ℝ)],
  ![(246828879918949816350293269/527024399006250000000:ℝ),(2130318955798664994399206783/1581073197018750000000:ℝ),(63756112026015170129262419/49408537406835937500:ℝ),(20323852149708434337127201/49408537406835937500:ℝ)]
]
theorem row005_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (20323852149708434337127201/92104189368729600000000000:ℝ) row005_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
#print axioms row005_identity
#print axioms row005_pos
end
end RH20261023Finite
