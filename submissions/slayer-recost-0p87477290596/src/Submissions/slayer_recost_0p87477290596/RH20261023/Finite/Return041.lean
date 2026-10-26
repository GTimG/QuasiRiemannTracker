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
def row041_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2958093649616992484292746681350279631/1928852202415965319357910156250:ℝ),(8635300992562692912283123487707837519/1928852202415965319357910156250:ℝ),(10079453967784097612232249979074820159/2314622642899158383229492187500:ℝ),(16333929162073233997730307983010003467/11573113214495791916147460937500:ℝ)],
  ![(71507968478198140891307452225994577791/26039504732615531811331787109375:ℝ),(208191800853332414858143873882369210649/26039504732615531811331787109375:ℝ),(2692687825389465766314402877371563074/347193396434873757484423828125:ℝ),(2417306349378163001085199584274031396/964426101207982659678955078125:ℝ)],
  ![(12770766429442283002027557850858309319/10415801893046212724532714843750:ℝ),(37068067184296913256883557110572524557/10415801893046212724532714843750:ℝ),(11947727482897056332729154881841867469/3471933964348737574844238281250:ℝ),(1282863815466646095495017009013765241/1157311321449579191614746093750:ℝ)]
]
theorem row041_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1282863815466646095495017009013765241/17259077350404465072734208000000000000:ℝ) row041_coefficients (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row041_coefficients,Fin.sum_univ_succ] <;> ring
theorem row041_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row041_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_coefficients]
#print axioms row041_identity
#print axioms row041_pos
end
end RH20261023Finite
