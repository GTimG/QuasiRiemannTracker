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
def row076_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1006152150077299662492600533381784733/13663286333336415396469042968750:ℝ),(2735062961490089171478969551589365261/13663286333336415396469042968750:ℝ),(4934057574295272395717260818903382859/27326572666672830792938085937500:ℝ),(491979025788047120935365865256490601/9108857555557610264312695312500:ℝ)],
  ![(912103450749447222426238229542047991/6831643166668207698234521484375:ℝ),(2427585161172458250595378390173510209/6831643166668207698234521484375:ℝ),(85427967836527151621677171024615126/273265726666728307929380859375:ℝ),(206683814773472214320850966713388644/2277214388889402566078173828125:ℝ)],
  ![(184790585363704216650338994219005759/2732657266667283079293808593750:ℝ),(486337433386480361578361650294556917/2732657266667283079293808593750:ℝ),(421994787736299994083559163510315807/2732657266667283079293808593750:ℝ),(40137013891933792725161338415754883/910885755555761026431269531250:ℝ)]
]
theorem row076_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (40137013891933792725161338415754883/13584112953139735808728104960000000000:ℝ) row076_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row076_coefficients,Fin.sum_univ_succ] <;> ring
theorem row076_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row076_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_coefficients]
#print axioms row076_identity
#print axioms row076_pos
end
end RH20261023Finite
