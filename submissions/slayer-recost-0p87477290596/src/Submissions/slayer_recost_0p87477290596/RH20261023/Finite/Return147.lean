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
def row147_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(64035455723186569300327407750048837703/138074216963984071875000000000000:ℝ),(51525891977072029077481712158945680311/46024738987994690625000000000000:ℝ),(4377682157115819775850129846867101363/5113859887554965625000000000000:ℝ),(27655198034097616015835777138623533571/138074216963984071875000000000000:ℝ)],
  ![(58406995781404606097958870633788171743/69037108481992035937500000000000:ℝ),(15016084782539599930472615910765358829/7670789831332448437500000000000:ℝ),(19253008961210270718653374828623323027/13807421696398407187500000000000:ℝ),(19527277544599560316972201580016557417/69037108481992035937500000000000:ℝ)],
  ![(62312939853732785714161378382456908963/138074216963984071875000000000000:ℝ),(9605568365534261157989611100701771091/9204947797598938125000000000000:ℝ),(1970665515909166609845741203568073961/2655273403153539843750000000000:ℝ),(690134039933184401876525148582339619/4602473898799469062500000000000:ℝ)]
]
theorem row147_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (19527277544599560316972201580016557417/65891582920124444285337600000000000000000:ℝ) row147_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row147_coefficients,Fin.sum_univ_succ] <;> ring
theorem row147_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row147_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row147_coefficients]
#print axioms row147_identity
#print axioms row147_pos
end
end RH20261023Finite
