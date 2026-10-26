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
def row044_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(288377899929128590656698165926125787/185282015275634765625000000:ℝ),(34420142940852254905442987859946291/7411280611025390625000000:ℝ),(570589028682857114475351805450444807/123521343517089843750000000:ℝ),(4203820287883079847905943371898307/2744918744824218750000000:ℝ)],
  ![(93217048140524585375634005848024211/30880335879272460937500000:ℝ),(55621567894006577766066411544806361/6176067175854492187500000:ℝ),(2880916318592898227154738268197929/321670165409088134765625:ℝ),(3055905841846997545071894062366453/1029344529309082031250000:ℝ)],
  ![(271110977471056670226524042216905757/185282015275634765625000000:ℝ),(32348132774692739157054083649629783/7411280611025390625000000:ℝ),(268028068803491352122323764191488351/61760671758544921875000000:ℝ),(5922041433649161059269849856680583/4117378117236328125000000:ℝ)]
]
theorem row044_identity (δ p : ℝ) : rowMargin .oldPeak .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (5922041433649161059269849856680583/62876459942386073600000000000000000:ℝ) row044_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row044_coefficients,Fin.sum_univ_succ] <;> ring
theorem row044_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldPeak .capP δ p := by
 rw [row044_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_coefficients]
#print axioms row044_identity
#print axioms row044_pos
end
end RH20261023Finite
