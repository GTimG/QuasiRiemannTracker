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
def row033_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2822133528410480427655067743710930419/277754717147899005987539062500:ℝ),(40950328672021916508027686148482832751/1388773585739495029937695312500:ℝ),(9897269326930318882441252309115934992/347193396434873757484423828125:ℝ),(3187331324388998579512800667844827328/347193396434873757484423828125:ℝ)],
  ![(6574269215755957320211847295443340017/347193396434873757484423828125:ℝ),(19044437340823785166234308788464194881/347193396434873757484423828125:ℝ),(18376409246795295271289637226012042432/347193396434873757484423828125:ℝ),(5906193465434446698525459043147437568/347193396434873757484423828125:ℝ)],
  ![(3054943230176699025648566826132298207/347193396434873757484423828125:ℝ),(1766397225490357197904431302123592323/69438679286974751496884765625:ℝ),(340174948150087589933932474942269632/13887735857394950299376953125:ℝ),(2727305843656949070467156303914827392/347193396434873757484423828125:ℝ)]
]
theorem row033_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (21307076903569914613024658624334589/161803850160041860056883200000000000:ℝ) row033_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row033_coefficients,Fin.sum_univ_succ] <;> ring
theorem row033_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row033_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_coefficients]
#print axioms row033_identity
#print axioms row033_pos
end
end RH20261023Finite
