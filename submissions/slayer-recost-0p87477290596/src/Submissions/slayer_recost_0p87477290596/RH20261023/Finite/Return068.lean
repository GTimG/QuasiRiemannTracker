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
def row068_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(483212695999068655219469442133780545493/104158018930462127245327148437500:ℝ),(467449556426529481963614500136812797207/34719339643487375748442382812500:ℝ),(112988142975625135478036307717223954424/8679834910871843937110595703125:ℝ),(21835850404375115589305813084665542848/5207900946523106362266357421875:ℝ)],
  ![(45445311716803899874829369621139641023/5207900946523106362266357421875:ℝ),(24380240546593898228821399312498823057/964426101207982659678955078125:ℝ),(635261902463209616678618642063867283808/26039504732615531811331787109375:ℝ),(68073162132361847385681631497938672128/8679834910871843937110595703125:ℝ)],
  ![(106771889613706248183510174461436446773/26039504732615531811331787109375:ℝ),(20581342083984835215423317972961359371/1735966982174368787422119140625:ℝ),(297333558976431031577160115258359855136/26039504732615531811331787109375:ℝ),(95384018339260392534417141238657161344/26039504732615531811331787109375:ℝ)]
]
theorem row068_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (745187643275471816675133915927009073/12135288762003139504266240000000000000:ℝ) row068_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row068_coefficients,Fin.sum_univ_succ] <;> ring
theorem row068_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row068_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_coefficients]
#print axioms row068_identity
#print axioms row068_pos
end
end RH20261023Finite
