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
def row042_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(78252038469680213592351598901666981/1482256122205078125000000000:ℝ),(77473829775648824296863526150612613/494085374068359375000000000:ℝ),(76698853870993236188247846217721837/494085374068359375000000000:ℝ),(75927110755713449266504559102994653/1482256122205078125000000000:ℝ)],
  ![(73795639364664134144714678454029141/741128061102539062500000000:ℝ),(24339069460355031725734370775357239/82347562344726562500000000:ℝ),(216726424501948309073792056908710947/741128061102539062500000000:ℝ),(2647053286052487321736940680908331/27449187448242187500000000:ℝ)],
  ![(69525661860091489807157665169621021/1482256122205078125000000000:ℝ),(68747059626444828385728168105496789/494085374068359375000000000:ℝ),(40783174453480322017347049973562169/296451224441015625000000000:ℝ),(67200355248158614736708410720941499/1482256122205078125000000000:ℝ)]
]
theorem row042_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (67200355248158614736708410720941499/707360174351843328000000000000000000:ℝ) row042_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row042_coefficients,Fin.sum_univ_succ] <;> ring
theorem row042_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row042_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_coefficients]
#print axioms row042_identity
#print axioms row042_pos
end
end RH20261023Finite
