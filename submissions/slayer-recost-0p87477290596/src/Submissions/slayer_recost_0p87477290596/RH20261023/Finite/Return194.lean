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
def row194_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(121383792162964469891403333764/19174292944117829736328125:ℝ),(58695154880552285153478076588/3834858588823565947265625:ℝ),(77041661302047327234704273644/6391430981372609912109375:ℝ),(6559222407371669536458419084/2130476993790869970703125:ℝ)],
  ![(196216297212975711169888557122/19174292944117829736328125:ℝ),(142570551248607348852637503526/6391430981372609912109375:ℝ),(284966150936125667995202937224/19174292944117829736328125:ℝ),(53470794403279332607178983768/19174292944117829736328125:ℝ)],
  ![(257487505634236557160691112349/51131447850980879296875000:ℝ),(1578755160428805149902253202743/153394343552942637890625000:ℝ),(114944958569543149367976920096/19174292944117829736328125:ℝ),(14158378128781214565454436884/19174292944117829736328125:ℝ)]
]
theorem row194_identity (δ p : ℝ) : rowMargin .newKink .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (3539594532195303641363609221/8935868176965021081600000000000:ℝ) row194_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row194_coefficients,Fin.sum_univ_succ] <;> ring
theorem row194_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newKink .capC δ p := by
 rw [row194_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row194_coefficients]
#print axioms row194_identity
#print axioms row194_pos
end
end RH20261023Finite
