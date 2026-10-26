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
def row139_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(199033806327691307656630906006298351/18217715111115220528625390625000:ℝ),(1382125078418299852191084652062024077/54653145333345661585876171875000:ℝ),(127077225541417100288061664359593696/6831643166668207698234521484375:ℝ),(28837651547903384420753883737015068/6831643166668207698234521484375:ℝ)],
  ![(54664603726339500319044217624312019/2277214388889402566078173828125:ℝ),(380296353264204411272905463914470089/6831643166668207698234521484375:ℝ),(280408452849375127016093415670979896/6831643166668207698234521484375:ℝ),(63862383715220908231974156191945864/6831643166668207698234521484375:ℝ)],
  ![(31991589922814051463878251152539674/2277214388889402566078173828125:ℝ),(226622286334690058104306439234973718/6831643166668207698234521484375:ℝ),(171693267176182735398384485586866924/6831643166668207698234521484375:ℝ),(40912917674133936157523827934512228/6831643166668207698234521484375:ℝ)]
]
theorem row139_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7209412886975846105188470934253767/3183776473392125580170649600000000000:ℝ) row139_coefficients (33/64:ℝ) (9/16:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row139_coefficients,Fin.sum_univ_succ] <;> ring
theorem row139_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row139_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row139_coefficients]
#print axioms row139_identity
#print axioms row139_pos
end
end RH20261023Finite
