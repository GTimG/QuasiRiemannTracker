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
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(93219383658796012783366758601/790536598509375000000:ℝ),(276774202625835927694082375803/790536598509375000000:ℝ),(273898395135238038719891461907/790536598509375000000:ℝ),(18068715233639624761835168941/158107319701875000000:ℝ)],
  ![(87444152169579946547688536377/395268299254687500000:ℝ),(259467099455300489690741842267/395268299254687500000:ℝ),(51322037119136106630197928019/79053659850937500000:ℝ),(16917447661991998001587266841/79053659850937500000:ℝ)],
  ![(81844192892418049111940640673/790536598509375000000:ℝ),(48537691083423236171233879151/158107319701875000000:ℝ),(239853086151203495447687882657/790536598509375000000:ℝ),(3160352945060214548138365103/31621463940375000000:ℝ)]
]
theorem row007_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 3 (3160352945060214548138365103/15090350386172657664000000000:ℝ) row007_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ] <;> ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
#print axioms row007_identity
#print axioms row007_pos
end
end RH20261023Finite
