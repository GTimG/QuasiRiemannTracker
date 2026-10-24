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
def row011_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(31736807297554330513618728613112102914/347193396434873757484423828125:ℝ),(18746148790170097609304821327804614584/69438679286974751496884765625:ℝ),(184521423158672921414242645175433200707/694386792869747514968847656250:ℝ),(12106702522830934913689079242456627139/138877358573949502993769531250:ℝ)],
  ![(59358188155063759355653145985068438744/347193396434873757484423828125:ℝ),(175163344986749252029837301124812010488/347193396434873757484423828125:ℝ),(172271720988526481741534816015341168684/347193396434873757484423828125:ℝ),(11293304991804843754525607351682019388/69438679286974751496884765625:ℝ)],
  ![(5537621651396033352415770210915461108/69438679286974751496884765625:ℝ),(16326643190727758132911784409363658364/69438679286974751496884765625:ℝ),(16042409269020284198925149928001892404/69438679286974751496884765625:ℝ),(5253383603602583597932017401428695148/69438679286974751496884765625:ℝ)]
]
theorem row011_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1313345900900645899483004350357173787/8284357128194143234912419840000000000:ℝ) row011_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row011_coefficients,Fin.sum_univ_succ] <;> ring
theorem row011_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row011_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_coefficients]
#print axioms row011_identity
#print axioms row011_pos
end
end RH20261023Finite
