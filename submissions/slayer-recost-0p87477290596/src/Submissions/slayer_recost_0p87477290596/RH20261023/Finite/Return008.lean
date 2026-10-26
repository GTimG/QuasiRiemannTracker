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
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(741265583697263774741739793/1646951246894531250:ℝ),(32998492967523559267308299711/24704268703417968750:ℝ),(130564209044703809894915728/98817074813671875:ℝ),(5380771524555674913773364592/12352134351708984375:ℝ)],
  ![(2869123369047363641790583997/3293902493789062500:ℝ),(127681517402886735585671638547/49408537406835937500:ℝ),(31564157288038074102343971232/12352134351708984375:ℝ),(10402990571244003862640751584/12352134351708984375:ℝ)],
  ![(1233185374752885475253421713/2927913327812500000:ℝ),(493744465636870130400577442423/395268299254687500000:ℝ),(15252054527508499443128434544/12352134351708984375:ℝ),(1005008155219008693367152464/2470426870341796875:ℝ)]
]
theorem row008_identity (δ p : ℝ) : rowMargin .oldSmall .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (62813009701188043335447029/294733405979934720000000000:ℝ) row008_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ] <;> ring
theorem row008_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capC δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
#print axioms row008_identity
#print axioms row008_pos
end
end RH20261023Finite
