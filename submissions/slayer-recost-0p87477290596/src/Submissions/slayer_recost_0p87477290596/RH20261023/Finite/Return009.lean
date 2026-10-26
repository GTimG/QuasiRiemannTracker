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
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(341349114689198231330232634039/98817074813671875000:ℝ),(40734069298025143801947202031/3952682992546875000:ℝ),(2025329132288234137002394963193/197634149627343750000:ℝ),(223774632255124469855166709907/65878049875781250000:ℝ)],
  ![(330014362147505471224515916909/49408537406835937500:ℝ),(196873600101005689241811322663/9881707481367187500:ℝ),(244675378290390703996609191208/12352134351708984375:ℝ),(54057979134006640166982678071/8234756234472656250:ℝ)],
  ![(318857532780596218615561503649/98817074813671875000:ℝ),(950919367798413847172063511083/98817074813671875000:ℝ),(189054978249852863913722704877/19763414962734375000:ℝ),(104404352077148897004037172317/32939024937890625000:ℝ)]
]
theorem row009_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (104404352077148897004037172317/503011679539088588800000000000:ℝ) row009_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ] <;> ring
theorem row009_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
#print axioms row009_identity
#print axioms row009_pos
end
end RH20261023Finite
