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
def row081_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(11500114457761327899487749823756308742/6831643166668207698234521484375:ℝ),(6456860190436892269795225592241843752/1366328633333641539646904296875:ℝ),(60267513307294183111893391002589602121/13663286333336415396469042968750:ℝ),(3739694861773405122345337448739881417/2732657266667283079293808593750:ℝ)],
  ![(21912922273098145474770469874325316232/6831643166668207698234521484375:ℝ),(61103941407323171148792960310676031464/6831643166668207698234521484375:ℝ),(56606100063406998425625132536143506052/6831643166668207698234521484375:ℝ),(3482875973293049160596328949646058164/1366328633333641539646904296875:ℝ)],
  ![(2162498249803558944140834469186383324/1366328633333641539646904296875:ℝ),(6001401447739509955965646465410975092/1366328633333641539646904296875:ℝ),(5529632077833481111259570999325677212/1366328633333641539646904296875:ℝ),(1690655083822085157474654018726085444/1366328633333641539646904296875:ℝ)]
]
theorem row081_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (422663770955521289368663504681521361/163009355437676829704737259520000000000:ℝ) row081_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row081_coefficients,Fin.sum_univ_succ] <;> ring
theorem row081_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row081_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row081_coefficients]
#print axioms row081_identity
#print axioms row081_pos
end
end RH20261023Finite
