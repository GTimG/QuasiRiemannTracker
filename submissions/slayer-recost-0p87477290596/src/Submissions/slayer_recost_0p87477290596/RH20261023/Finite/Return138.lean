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
def row138_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(6101311376953877467165955209193956669/27326572666672830792938085937500:ℝ),(3127135300056260614782100779831699881/5465314533334566158587617187500:ℝ),(3280859028302607479966823290617805264/6831643166668207698234521484375:ℝ),(179372189320972167145121478351896416/1366328633333641539646904296875:ℝ)],
  ![(3114584075014363515768075030630020243/6831643166668207698234521484375:ℝ),(7947254749825779283121535746132585219/6831643166668207698234521484375:ℝ),(6632027234494090151150493400366127872/6831643166668207698234521484375:ℝ),(1798504215011285304157820115332312896/6831643166668207698234521484375:ℝ)],
  ![(1639216659986016292154267765251894717/6831643166668207698234521484375:ℝ),(4185296033014797080113715154978885133/6831643166668207698234521484375:ℝ),(3495274591746178454020723712605222688/6831643166668207698234521484375:ℝ),(948748752460955767202641167409482272/6831643166668207698234521484375:ℝ)]
]
theorem row138_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5605380916280380223285046198496763/2547021178713700464136519680000000000:ℝ) row138_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row138_coefficients,Fin.sum_univ_succ] <;> ring
theorem row138_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row138_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row138_coefficients]
#print axioms row138_identity
#print axioms row138_pos
end
end RH20261023Finite
