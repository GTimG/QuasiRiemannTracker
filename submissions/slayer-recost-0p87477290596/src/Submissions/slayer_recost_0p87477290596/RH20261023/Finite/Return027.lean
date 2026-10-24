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
def row027_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(8432042373189576059373468935194677121/2777547171478990059875390625000:ℝ),(24560570510809918848879123983167628963/2777547171478990059875390625000:ℝ),(23835076893394724086295849714606021563/2777547171478990059875390625000:ℝ),(2568835831638207697273003795127689907/925849057159663353291796875000:ℝ)],
  ![(7412335604389816179782554695345318193/1388773585739495029937695312500:ℝ),(21525372873453166836159932178953328131/1388773585739495029937695312500:ℝ),(20824097240647851315790829509387622743/1388773585739495029937695312500:ℝ),(447400972309251108929676694426974187/92584905715966335329179687500:ℝ)],
  ![(6458448404388007391477341497352915993/2777547171478990059875390625000:ℝ),(18688583752571618330540743922692533203/2777547171478990059875390625000:ℝ),(18012434347657566463194257325699242809/2777547171478990059875390625000:ℝ),(1927416357944549365371907710015708533/925849057159663353291796875000:ℝ)]
]
theorem row027_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1927416357944549365371907710015708533/13807261880323572058187366400000000000:ℝ) row027_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row027_coefficients,Fin.sum_univ_succ] <;> ring
theorem row027_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row027_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_coefficients]
#print axioms row027_identity
#print axioms row027_pos
end
end RH20261023Finite
