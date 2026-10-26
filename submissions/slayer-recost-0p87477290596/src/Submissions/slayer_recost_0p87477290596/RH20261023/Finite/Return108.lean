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
def row108_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(22724520535819497684976681789795703/109306290666691323171752343750000:ℝ),(11121827063597906245763219210990417/21861258133338264634350468750000:ℝ),(44877717350531253882040980238810793/109306290666691323171752343750000:ℝ),(3978021902668422256705859491218137/36435430222230441057250781250000:ℝ)],
  ![(21687235870127207547963468939086543/54653145333345661585876171875000:ℝ),(1915396562853791975469688648098157/2186125813333826463435046875000:ℝ),(33344293479538846508827586438831279/54653145333345661585876171875000:ℝ),(2352686662595774772640952641821299/18217715111115220528625390625000:ℝ)],
  ![(39149691737717760002998035654695243/109306290666691323171752343750000:ℝ),(91667441435644510379055290288700061/109306290666691323171752343750000:ℝ),(6967005777530431180830478079570267/10930629066669132317175234375000:ℝ),(1418289595131388825338212857224821/9108857555557610264312695312500:ℝ)]
]
theorem row108_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2352686662595774772640952641821299/530629412232020930028441600000000000:ℝ) row108_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row108_coefficients,Fin.sum_univ_succ] <;> ring
theorem row108_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row108_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row108_coefficients]
#print axioms row108_identity
#print axioms row108_pos
end
end RH20261023Finite
