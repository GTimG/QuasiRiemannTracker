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
def row043_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1873298213795039780059438310232679/9264100763781738281250000:ℝ),(9270024921806758467370587470802497/15440167939636230468750000:ℝ),(573372625136845419791086193013878/965010496227264404296875:ℝ),(567393894382718978009847900213878/2895031488681793212890625:ℝ)],
  ![(12117264169224176071059085633108717/30880335879272460937500000:ℝ),(107897814003180700535684298817369031/92641007637817382812500000:ℝ),(667157423143685124298768729261652/579006297736358642578125:ℝ),(8147955140620705454929619158292/21444677693939208984375:ℝ)],
  ![(141043743394908167177384604772048027/741128061102539062500000000:ℝ),(83700237484253554260636890407456799/148225612220507812500000000:ℝ),(1616762868924285559936076156919742/2895031488681793212890625:ℝ),(532944728196318356319670503539914/2895031488681793212890625:ℝ)]
]
theorem row043_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (266472364098159178159835251769957/2763125681061888000000000000000000:ℝ) row043_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row043_coefficients,Fin.sum_univ_succ] <;> ring
theorem row043_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row043_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_coefficients]
#print axioms row043_identity
#print axioms row043_pos
end
end RH20261023Finite
