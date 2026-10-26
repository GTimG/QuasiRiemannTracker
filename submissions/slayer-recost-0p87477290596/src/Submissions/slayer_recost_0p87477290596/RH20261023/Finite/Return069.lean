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
def row069_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(32835393318656360900748348568009134037/208316037860924254490654296875000:ℝ),(92497497380634716385308501025176387909/208316037860924254490654296875000:ℝ),(10837709634577268339759149057538754754/26039504732615531811331787109375:ℝ),(675924375810776831092657055742632104/5207900946523106362266357421875:ℝ)],
  ![(7340384254599990777969259920384397241/26039504732615531811331787109375:ℝ),(20544365590892126594492677827830062441/26039504732615531811331787109375:ℝ),(19123218027591984443020486424778130384/26039504732615531811331787109375:ℝ),(5918528150697470992913407306394965184/26039504732615531811331787109375:ℝ)],
  ![(1093370524307522103113302224768583934/8679834910871843937110595703125:ℝ),(3037818865200160254802780239815000606/8679834910871843937110595703125:ℝ),(561040717768000720997396292714477472/1735966982174368787422119140625:ℝ),(860626422383296792645928682900970688/8679834910871843937110595703125:ℝ)]
]
theorem row069_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13447287849739012385092635670327667/252818515875065406338880000000000000:ℝ) row069_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row069_coefficients,Fin.sum_univ_succ] <;> ring
theorem row069_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row069_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_coefficients]
#print axioms row069_identity
#print axioms row069_pos
end
end RH20261023Finite
