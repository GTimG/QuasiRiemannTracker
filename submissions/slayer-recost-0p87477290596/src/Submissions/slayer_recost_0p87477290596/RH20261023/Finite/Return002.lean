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
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(1725795562549499360842581088421431/5555094342957980119750781250000:ℝ),(4646620933825557975586711104272419/5555094342957980119750781250000:ℝ),(8308464686447777627159394011418901/11110188685915960239501562500000:ℝ),(98606540380213287952952109188677/444407547436638409580062500000:ℝ)],
  ![(1053708174858287457010414349287879/2777547171478990059875390625000:ℝ),(2667411744786570267591680593458097/2777547171478990059875390625000:ℝ),(2228235054971762538233273897555573/2777547171478990059875390625000:ℝ),(122576210130630305760935280677071/555509434295798011975078125000:ℝ)],
  ![(559383806141730917010272610154327/5555094342957980119750781250000:ℝ),(1279962444703267906627390557771037/5555094342957980119750781250000:ℝ),(189281835598039355762502813875107/1111018868591596023950156250000:ℝ),(8901186825920135660029344870353/222203773718319204790031250000:ℝ)]
]
theorem row002_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (8901186825920135660029344870353/101127406350026162535552000000000:ℝ) row002_coefficients (3/8:ℝ) (3/4:ℝ) (0/1:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0/1:ℝ) (1/4:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
#print axioms row002_identity
#print axioms row002_pos
end
end RH20261023Finite
