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
def row035_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2090432930017926337015208421995489/3703396228638653413167187500000:ℝ),(15784914268087950986551284817895123/11110188685915960239501562500000:ℝ),(3283885134457472597614377703823401/2777547171478990059875390625000:ℝ),(901767787570691156331467503346237/2777547171478990059875390625000:ℝ)],
  ![(177133109243518899800970407491133/231462264289915838322949218750:ℝ),(1259991948662422820143954721670913/694386792869747514968847656250:ℝ),(488972428933933846300519211160679/347193396434873757484423828125:ℝ),(123438292675254636794499024061922/347193396434873757484423828125:ℝ)],
  ![(18679090984887923930607768425563/77154088096638612774316406250:ℝ),(364925373568880643971253145440671/694386792869747514968847656250:ℝ),(126440920439614801784189092769681/347193396434873757484423828125:ℝ),(27208925892006038062631852964379/347193396434873757484423828125:ℝ)]
]
theorem row035_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (27208925892006038062631852964379/632046289687663515847200000000000:ℝ) row035_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row035_coefficients,Fin.sum_univ_succ] <;> ring
theorem row035_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_coefficients]
#print axioms row035_identity
#print axioms row035_pos
end
end RH20261023Finite
