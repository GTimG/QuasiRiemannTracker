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
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(590682541423377032487134873898259/8888150948732768191601250000000:ℝ),(310697455265184870819536436415973/1777630189746553638320250000000:ℝ),(1334926928381717610733959742464953/8888150948732768191601250000000:ℝ),(372122193479170289123412434283347/8888150948732768191601250000000:ℝ)],
  ![(2103562300451017894771482630357743/22220377371831920479003125000000:ℝ),(5175049445637877463429444155916813/22220377371831920479003125000000:ℝ),(4128284935798931305691961886179577/22220377371831920479003125000000:ℝ),(1056797790612071737034000360620507/22220377371831920479003125000000:ℝ)],
  ![(1431474912759805990939315891224191/44440754743663840958006250000000:ℝ),(129315729225341510357435334067553/1777630189746553638320250000000:ℝ),(2324870375872741324789891279420699/44440754743663840958006250000000:ℝ),(103370064087539352280799763791213/8888150948732768191601250000000:ℝ)]
]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (103370064087539352280799763791213/505637031750130812677760000000000:ℝ) row001_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
#print axioms row001_identity
#print axioms row001_pos
end
end RH20261023Finite
