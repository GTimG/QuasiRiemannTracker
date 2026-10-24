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
def row198_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(219414847072517238918508665920638/19174292944117829736328125:ℝ),(7645041405901309393002066631034/255657239254904396484375:ℝ),(489840234693692571142608814007153/19174292944117829736328125:ℝ),(45292325441203868528654160866747/6391430981372609912109375:ℝ)],
  ![(418695067746509725860144714657556/19174292944117829736328125:ℝ),(216133509795355820134741909090492/3834858588823565947265625:ℝ),(907961378951719819243312451529088/19174292944117829736328125:ℝ),(81996299240483481476582540244728/6391430981372609912109375:ℝ)],
  ![(23293309638617757150780331475362/2130476993790869970703125:ℝ),(538241857218858232757897564610086/19174292944117829736328125:ℝ),(89789554394972360111890076717194/3834858588823565947265625:ℝ),(13371744611507042462063978028238/2130476993790869970703125:ℝ)]
]
theorem row198_identity (δ p : ℝ) : rowMargin .newKink .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (6685872305753521231031989014119/16267251579043878377881600000000000:ℝ) row198_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row198_coefficients,Fin.sum_univ_succ] <;> ring
theorem row198_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newKink .capP δ p := by
 rw [row198_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row198_coefficients]
#print axioms row198_identity
#print axioms row198_pos
end
end RH20261023Finite
