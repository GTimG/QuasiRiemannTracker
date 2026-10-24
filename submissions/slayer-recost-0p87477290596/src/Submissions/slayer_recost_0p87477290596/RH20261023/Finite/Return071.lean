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
def row071_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(764647791488769129971693863444777/174890065066706117074803750000000:ℝ),(408364428659192198638003702297919/34978013013341223414960750000000:ℝ),(1789700912125614596464955432644859/174890065066706117074803750000000:ℝ),(512526560318422733246630784600041/174890065066706117074803750000000:ℝ)],
  ![(1052703642093972720673027389823229/437225162666765292687009375000000:ℝ),(2627309916705106951738709434000439/437225162666765292687009375000000:ℝ),(2209848442913452081233026094788731/437225162666765292687009375000000:ℝ),(635242168302317850167344050611521/437225162666765292687009375000000:ℝ)],
  ![(1779969628078222132983660462422573/874450325333530585374018750000000:ℝ),(110571845860470943155653588952659/34978013013341223414960750000000:ℝ),(1282298150862083702753077309512097/874450325333530585374018750000000:ℝ),(35979582343325024135484609623639/174890065066706117074803750000000:ℝ)]
]
theorem row071_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (35979582343325024135484609623639/9949301479350392438033280000000000:ℝ) row071_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row071_coefficients,Fin.sum_univ_succ] <;> ring
theorem row071_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row071_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row071_coefficients]
#print axioms row071_identity
#print axioms row071_pos
end
end RH20261023Finite
