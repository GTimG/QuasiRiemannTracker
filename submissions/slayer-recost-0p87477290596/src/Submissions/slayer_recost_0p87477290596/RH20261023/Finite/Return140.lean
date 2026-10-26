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
def row140_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1162453920809104216243848238908019/24290286814820294038167187500000:ℝ),(18495438973091429023614494112823679/218612581333382646343504687500000:ℝ),(4694436100752807633916696478759561/109306290666691323171752343750000:ℝ),(544926322047166567017794622433807/109306290666691323171752343750000:ℝ)],
  ![(823761069676643114441848657170797/6072571703705073509541796875000:ℝ),(13644930377274185089247553059620111/54653145333345661585876171875000:ℝ),(7514475516832141958136719132425451/54653145333345661585876171875000:ℝ),(1106284185579884194613841487342513/54653145333345661585876171875000:ℝ)],
  ![(1323236019688773601206881244419777/12145143407410147019083593750000:ℝ),(23981425720757700403266680210145259/109306290666691323171752343750000:ℝ),(15448137410799257173526476232513843/109306290666691323171752343750000:ℝ),(3139688425816704908785777222146577/109306290666691323171752343750000:ℝ)]
]
theorem row140_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (544926322047166567017794622433807/198986029587007848760665600000000000:ℝ) row140_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row140_coefficients,Fin.sum_univ_succ] <;> ring
theorem row140_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row140_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row140_coefficients]
#print axioms row140_identity
#print axioms row140_pos
end
end RH20261023Finite
