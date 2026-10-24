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
def row061_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1823340410768395384714503104634902719/34719339643487375748442382812500:ℝ),(5194415017020313587950392645972556407/34719339643487375748442382812500:ℝ),(29562831551023983114945900380943631067/208316037860924254490654296875000:ℝ),(9335847140328854476149001609480208939/208316037860924254490654296875000:ℝ)],
  ![(1495998319320947034713293344239128213/17359669821743687874221191406250:ℝ),(4219965000458490011390417205020070491/17359669821743687874221191406250:ℝ),(5941689318056943542294300714841276202/26039504732615531811331787109375:ℝ),(371115652879108650292829293327722557/5207900946523106362266357421875:ℝ)],
  ![(1229097437994133567789644312198666457/34719339643487375748442382812500:ℝ),(1691485563873229559226877475918011/17145352910364136172070312500:ℝ),(3173288127758634398175972795995083129/34719339643487375748442382812500:ℝ),(976998473345409447879615453834777311/34719339643487375748442382812500:ℝ)]
]
theorem row061_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (976998473345409447879615453834777311/16180385016004186005688320000000000000:ℝ) row061_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row061_coefficients,Fin.sum_univ_succ] <;> ring
theorem row061_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row061_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_coefficients]
#print axioms row061_identity
#print axioms row061_pos
end
end RH20261023Finite
