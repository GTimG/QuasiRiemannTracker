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
def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(70244976338338882039701616507785817/11110188685915960239501562500000:ℝ),(39225468497621629925619415273413487/2222037737183192047900312500000:ℝ),(182094180147372111483697642209639907/11110188685915960239501562500000:ℝ),(18735070753347177033304285783452763/3703396228638653413167187500000:ℝ)],
  ![(50414553807154415780270417740646377/5555094342957980119750781250000:ℝ),(27541279541962414373239890329080399/1111018868591596023950156250000:ℝ),(124853024385667123785205115636320231/5555094342957980119750781250000:ℝ),(12517092625555832835397364743854871/1851698114319326706583593750000:ℝ)],
  ![(34253720461479812453691733851052177/11110188685915960239501562500000:ℝ),(90645232976145893174732837632899419/11110188685915960239501562500000:ℝ),(3171540852459319995574964306702713/444407547436638409580062500000:ℝ),(7627384962434655126235674211906861/3703396228638653413167187500000:ℝ)]
]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7627384962434655126235674211906861/53934616720013953352294400000000000:ℝ) row003_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row003_coefficients,Fin.sum_univ_succ] <;> ring
theorem row003_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row003_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]
#print axioms row003_identity
#print axioms row003_pos
end
end RH20261023Finite
