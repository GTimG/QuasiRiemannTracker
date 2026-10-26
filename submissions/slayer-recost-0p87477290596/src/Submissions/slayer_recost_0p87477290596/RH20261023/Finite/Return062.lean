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
def row062_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(284174907419875316511726902939550321643/208316037860924254490654296875000:ℝ),(827640080179027234551198379978602896929/208316037860924254490654296875000:ℝ),(267714128488970783125758843559221484643/69438679286974751496884765625000:ℝ),(9617595022778739024454770649809699209/7715408809663861277431640625000:ℝ)],
  ![(84519454031976137662349417017579398953/34719339643487375748442382812500:ℝ),(245411406817211946752098008886858848491/34719339643487375748442382812500:ℝ),(79133298535988444382967217819634175541/11573113214495791916147460937500:ℝ),(5100477037026236594048451423683205139/2314622642899158383229492187500:ℝ)],
  ![(9030700467755089227043111198438633451/8332641514436970179626171875000:ℝ),(653267804780294226760487161167493452017/208316037860924254490654296875000:ℝ),(209886266340530784930714484893352907953/69438679286974751496884765625000:ℝ),(22461767550329626746436368411121512013/23146226428991583832294921875000:ℝ)]
]
theorem row062_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (22461767550329626746436368411121512013/345181547008089301454684160000000000000:ℝ) row062_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row062_coefficients,Fin.sum_univ_succ] <;> ring
theorem row062_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row062_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_coefficients]
#print axioms row062_identity
#print axioms row062_pos
end
end RH20261023Finite
