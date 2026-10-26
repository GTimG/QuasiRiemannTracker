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
def row196_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(23079310164232817293398842923603/38348585888235659472656250:ℝ),(58687083588614212200861523299209/38348585888235659472656250:ℝ),(48454914036688648259868633693301/38348585888235659472656250:ℝ),(856476040820483556827063554513/2556572392549043964843750:ℝ)],
  ![(21218316222536153091523024687051/19174292944117829736328125:ℝ),(52398396533809342269573272201081/19174292944117829736328125:ℝ),(184328271175452131577681313067/85219079751634798828125:ℝ),(2058756140640708085385609585209/3834858588823565947265625:ℝ)],
  ![(22010854635425505173124350372959/38348585888235659472656250:ℝ),(10801233427677295034572905173101/7669717177647131894531250:ℝ),(21162812407726314677518525831138/19174292944117829736328125:ℝ),(1033031231249165935529687616973/3834858588823565947265625:ℝ)]
]
theorem row196_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (2058756140640708085385609585209/3660131605284872635023360000000000:ℝ) row196_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row196_coefficients,Fin.sum_univ_succ] <;> ring
theorem row196_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row196_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row196_coefficients]
#print axioms row196_identity
#print axioms row196_pos
end
end RH20261023Finite
