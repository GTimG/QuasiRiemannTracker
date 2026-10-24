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
def row026_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(32895673104016788185122151683930283/277754717147899005987539062500:ℝ),(93835121159235576708319477471568459/277754717147899005987539062500:ℝ),(178224209925395672634672705816562013/555509434295798011975078125000:ℝ),(56343250771970185339718890178785661/555509434295798011975078125000:ℝ)],
  ![(131155308147346375204404923705013709/694386792869747514968847656250:ℝ),(370624677036803393593332898413008659/694386792869747514968847656250:ℝ),(174233924211676858123343311173583318/347193396434873757484423828125:ℝ),(54496145202466483556040577725835843/347193396434873757484423828125:ℝ)],
  ![(101817062168619308949434780513325649/1388773585739495029937695312500:ℝ),(56833414641343143868359652403832959/277754717147899005987539062500:ℝ),(263597614922665301367397872703278161/1388773585739495029937695312500:ℝ),(16248035385962482816044280114487803/277754717147899005987539062500:ℝ)]
]
theorem row026_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (16248035385962482816044280114487803/129443080128033488045506560000000000:ℝ) row026_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row026_coefficients,Fin.sum_univ_succ] <;> ring
theorem row026_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row026_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_coefficients]
#print axioms row026_identity
#print axioms row026_pos
end
end RH20261023Finite
