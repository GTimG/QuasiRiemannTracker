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
def row197_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(7254921506427722207888078800472/3834858588823565947265625:ℝ),(89000557231006937113019634526648/19174292944117829736328125:ℝ),(2792511482114118095376092751104/766971717764713189453125:ℝ),(17086837353984626310823078253312/19174292944117829736328125:ℝ)],
  ![(4496077166148915795194998481428/1278286196274521982421875:ℝ),(161318885720330460330085080859948/19174292944117829736328125:ℝ),(40537323056920816244627037328384/6391430981372609912109375:ℝ),(27734240942665725331721008346624/19174292944117829736328125:ℝ)],
  ![(12983996298490190041163180014691/7669717177647131894531250:ℝ),(50778051180956384309087400001061/12782861962745219824218750:ℝ),(55616607078968402479950758449984/19174292944117829736328125:ℝ),(264656023416873358205057966336/426095398758173994140625:ℝ)]
]
theorem row197_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1033812591472161555488507681/3177197574032007495680000000000:ℝ) row197_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row197_coefficients,Fin.sum_univ_succ] <;> ring
theorem row197_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row197_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row197_coefficients]
#print axioms row197_identity
#print axioms row197_pos
end
end RH20261023Finite
