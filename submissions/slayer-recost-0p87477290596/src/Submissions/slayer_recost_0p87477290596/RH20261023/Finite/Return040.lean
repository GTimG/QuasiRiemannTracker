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
def row040_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(960139408705666206356307073721/3705640305512695312500000:ℝ),(69701967036885942706642817459287/92641007637817382812500000:ℝ),(67425342692368134804168426124393/92641007637817382812500000:ℝ),(21726860873123847256433285508131/92641007637817382812500000:ℝ)],
  ![(86588721198299761562929227749449/185282015275634765625000000:ℝ),(250513168300409189268156944047841/185282015275634765625000000:ℝ),(60349768052177485250467980011897/46320503818908691406250000:ℝ),(19368656276650128324161050937299/46320503818908691406250000:ℝ)],
  ![(69235973665851335019978423202027/329390249378906250000000000:ℝ),(4432610258323991730578231422647/7319783319531250000000000:ℝ),(5980044107354421190517837219551/10293445293090820312500000:ℝ),(212256678738240226529613889613/1143716143676757812500000:ℝ)]
]
theorem row040_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (1910310108644162038766525006517/19188372785152000000000000000000:ℝ) row040_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row040_coefficients,Fin.sum_univ_succ] <;> ring
theorem row040_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row040_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_coefficients]
#print axioms row040_identity
#print axioms row040_pos
end
end RH20261023Finite
