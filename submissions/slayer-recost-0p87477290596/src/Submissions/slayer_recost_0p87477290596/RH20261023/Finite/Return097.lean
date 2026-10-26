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
def row097_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1865902089578451918588522766093900277/27326572666672830792938085937500:ℝ),(4917363041689032872039014974657097231/27326572666672830792938085937500:ℝ),(4273936585187229197090990106814686131/27326572666672830792938085937500:ℝ),(407368884233141177946657658792163059/9108857555557610264312695312500:ℝ)],
  ![(377920208343319928047887249839972377/2732657266667283079293808593750:ℝ),(4925567053208919986631874697255645983/13663286333336415396469042968750:ℝ),(4222486070723871556842723190687087901/13663286333336415396469042968750:ℝ),(395371393605534676556569109522934601/4554428777778805132156347656250:ℝ)],
  ![(425019268929719992734797564618251717/5465314533334566158587617187500:ℝ),(5556930676883956057584776465284453591/27326572666672830792938085937500:ℝ),(9564488448532142181959183252209036/54653145333345661585876171875:ℝ),(224993904295712183035027971407095499/4554428777778805132156347656250:ℝ)]
]
theorem row097_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (395371393605534676556569109522934601/135841129531397358087281049600000000000:ℝ) row097_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row097_coefficients,Fin.sum_univ_succ] <;> ring
theorem row097_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row097_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row097_coefficients]
#print axioms row097_identity
#print axioms row097_pos
end
end RH20261023Finite
