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
def row036_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(99042821497323849402220323921593459/3333056605774788071850468750000000:ℝ),(86827900295070162953874024538178099/1111018868591596023950156250000000:ℝ),(74612979092816476505527725154762739/1111018868591596023950156250000000:ℝ),(62398057890562790057181425771347379/3333056605774788071850468750000000:ℝ)],
  ![(66537293412564190283257167514220723/1666528302887394035925234375000000:ℝ),(55050253009760523670499055956659907/555509434295798011975078125000000:ℝ),(133103374936202433148831243103735773/1666528302887394035925234375000000:ℝ),(153288485864378010758183301102119/7406792457277306826334375000000:ℝ)],
  ![(47363991750903683451695886106847987/3333056605774788071850468750000000:ℝ),(7110652032323688517442446230993823/222203773718319204790031250000000:ℝ),(76964333196451272620057247337942379/3333056605774788071850468750000000:ℝ),(17325009624983199905917064979883021/3333056605774788071850468750000000:ℝ)]
]
theorem row036_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (17325009624983199905917064979883021/189613886906299054754160000000000000:ℝ) row036_coefficients (0/1:ℝ) (3/8:ℝ) (0/1:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row036_coefficients,Fin.sum_univ_succ] <;> ring
theorem row036_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0/1:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row036_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_coefficients]
#print axioms row036_identity
#print axioms row036_pos
end
end RH20261023Finite
