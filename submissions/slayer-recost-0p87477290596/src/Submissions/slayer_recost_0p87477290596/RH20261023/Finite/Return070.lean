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
def row070_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(215569585269983387206306425714270629/833264151443697017962617187500000:ℝ),(19732237444918205238789449303605363/30861635238655445109726562500000:ℝ),(302143998870787463301362367056656/578655660724789595807373046875:ℝ),(29278394811678457250876127332127617/208316037860924254490654296875000:ℝ)],
  ![(2277277281294887397305715598451167/5786556607247895958073730468750:ℝ),(1898195127392342102089341460519099/2083160378609242544906542968750:ℝ),(17915383997477750138318418923876558/26039504732615531811331787109375:ℝ),(1457093296288712274763329349306024/8679834910871843937110595703125:ℝ)],
  ![(8514802064993674060491042656879809/52079009465231063622663574218750:ℝ),(18477500969828518763150350822356889/52079009465231063622663574218750:ℝ),(6407224899299298389904798417595463/26039504732615531811331787109375:ℝ),(1382933592192322488050222459856923/26039504732615531811331787109375:ℝ)]
]
theorem row070_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1382933592192322488050222459856923/47403471726574763688540000000000000:ℝ) row070_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row070_coefficients,Fin.sum_univ_succ] <;> ring
theorem row070_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row070_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_coefficients]
#print axioms row070_identity
#print axioms row070_pos
end
end RH20261023Finite
