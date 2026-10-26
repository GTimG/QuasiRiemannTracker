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
def row145_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(3899929279765900688014164452401873/690371084819920359375000000000:ℝ),(229816018929915251964232830356855231/17259277120498008984375000000000:ℝ),(174637439771100601106327768931812609/17259277120498008984375000000000:ℝ),(42319652835332866342449049885004203/17259277120498008984375000000000:ℝ)],
  ![(310573285753807775699400594398074337/34518554240996017968750000000000:ℝ),(645657897134004506219566580820405433/34518554240996017968750000000000:ℝ),(98093769269840374856282121691574161/8629638560249004492187500000000:ℝ),(112776507281820411230241142409381/67949909923220507812500000000:ℝ)],
  ![(274872506170793691281576174974700851/61366318650659587500000000000000:ℝ),(319372115886627697526142450396950597/36819791190395752500000000000000:ℝ),(25477878818770871241154425316067989/5753092373499336328125000000000:ℝ),(1345283164997202060342433845422663/5753092373499336328125000000000:ℝ)]
]
theorem row145_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1345283164997202060342433845422663/10724541490905671270400000000000000000:ℝ) row145_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row145_coefficients,Fin.sum_univ_succ] <;> ring
theorem row145_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row145_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row145_coefficients]
#print axioms row145_identity
#print axioms row145_pos
end
end RH20261023Finite
