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
def row148_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2323941322740803226079057151027861327/1725927712049800898437500000000:ℝ),(8684279822517201950719608549490951961/2876546186749668164062500000000:ℝ),(60877880731270019760767021091245569/29964022778642376708984375000:ℝ),(96865524898692999041792568154536707/269676205007781390380859375000:ℝ)],
  ![(14137886907900853316029518842411502821/5753092373499336328125000000000:ℝ),(90790164303889630341205376773594345903/17259277120498008984375000000000:ℝ),(86731978279941228461432886426065869/26967620500778139038085937500:ℝ),(3714563811966310324062618263709541/8989206833592713012695312500:ℝ)],
  ![(162687794735969958420023820145534698851/138074216963984071875000000000000:ℝ),(67425872601521955583436727842844194887/27614843392796814375000000000000:ℝ),(372987846971584921206471352624566823/269676205007781390380859375000:ℝ),(32281658941038398751081081006038941/269676205007781390380859375000:ℝ)]
]
theorem row148_identity (δ p : ℝ) : rowMargin .newTop .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (32281658941038398751081081006038941/514777991563472220979200000000000000000:ℝ) row148_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row148_coefficients,Fin.sum_univ_succ] <;> ring
theorem row148_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capC δ p := by
 rw [row148_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row148_coefficients]
#print axioms row148_identity
#print axioms row148_pos
end
end RH20261023Finite
