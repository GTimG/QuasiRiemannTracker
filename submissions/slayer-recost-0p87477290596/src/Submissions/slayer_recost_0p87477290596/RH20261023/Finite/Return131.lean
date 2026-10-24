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
def row131_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(75932837862151206377513372317733231/21861258133338264634350468750000:ℝ),(186176609898898807310191806490531013/21861258133338264634350468750000:ℝ),(148467771492130742246011294731081583/21861258133338264634350468750000:ℝ),(38150203379938199353227876183283801/21861258133338264634350468750000:ℝ)],
  ![(420347464779327224959094668093013683/54653145333345661585876171875000:ℝ),(1014788427403972173667778959494651433/54653145333345661585876171875000:ℝ),(791559494011542527648181949344547157/54653145333345661585876171875000:ℝ),(196675754934227927178867751692909407/54653145333345661585876171875000:ℝ)],
  ![(579730107239956690337265809872756963/109306290666691323171752343750000:ℝ),(288280840822136209094746308529705013/21861258133338264634350468750000:ℝ),(1170704096979619095732636788137885457/109306290666691323171752343750000:ℝ),(61699733673138231696683033572423471/21861258133338264634350468750000:ℝ)]
]
theorem row131_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (38150203379938199353227876183283801/10188084714854801856546078720000000000:ℝ) row131_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row131_coefficients,Fin.sum_univ_succ] <;> ring
theorem row131_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row131_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row131_coefficients]
#print axioms row131_identity
#print axioms row131_pos
end
end RH20261023Finite
