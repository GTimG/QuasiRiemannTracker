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
def row046_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1070991855516875626809732514457435092822/26039504732615531811331787109375:ℝ),(1054586180215695881358842785975662102008/8679834910871843937110595703125:ℝ),(6229806531784205975933102135764349155489/52079009465231063622663574218750:ℝ),(45428249417168646117678733593903052313/1157311321449579191614746093750:ℝ)],
  ![(2015793234767107424079380064771465547592/26039504732615531811331787109375:ℝ),(1983315715407007820119942527471624502328/8679834910871843937110595703125:ℝ),(1951085619869726685751511715394845055564/8679834910871843937110595703125:ℝ),(76764036336686650687217507790082588292/1041580189304621272453271484375:ℝ)],
  ![(189517883897172619636698609085499495804/5207900946523106362266357421875:ℝ),(62100752915864895950168864893251884468/578655660724789595807373046875:ℝ),(549336002012106347548440089073607358012/5207900946523106362266357421875:ℝ),(179946894957221455865866289510464893604/5207900946523106362266357421875:ℝ)]
]
theorem row046_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (44986723739305363966466572377616223401/621326784614560742618431488000000000000:ℝ) row046_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row046_coefficients,Fin.sum_univ_succ] <;> ring
theorem row046_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row046_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_coefficients]
#print axioms row046_identity
#print axioms row046_pos
end
end RH20261023Finite
