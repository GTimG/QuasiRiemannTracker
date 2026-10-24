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
def row034_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(318978105695952110667627215656545157/925849057159663353291796875000:ℝ),(2699112586115468035035824798567352719/2777547171478990059875390625000:ℝ),(316591031100817882791925205301532652/347193396434873757484423828125:ℝ),(98812506767327991410915840062755496/347193396434873757484423828125:ℝ)],
  ![(23269400474656395374020277700571811/38577044048319306387158203125:ℝ),(586905751473939801061370670937326203/347193396434873757484423828125:ℝ),(546895915687874148308063682362829472/347193396434873757484423828125:ℝ),(169401152402121697972385027918149568/347193396434873757484423828125:ℝ)],
  ![(30278748466131167555720457404318938/115731132144957919161474609375:ℝ),(252631652061952448874750445652909326/347193396434873757484423828125:ℝ),(233446942079546748595683492996873728/347193396434873757484423828125:ℝ),(71644108461231325493281428931921216/347193396434873757484423828125:ℝ)]
]
theorem row034_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1119439194706739460832522327061269/10112740635002616253555200000000000:ℝ) row034_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row034_coefficients,Fin.sum_univ_succ] <;> ring
theorem row034_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row034_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_coefficients]
#print axioms row034_identity
#print axioms row034_pos
end
end RH20261023Finite
