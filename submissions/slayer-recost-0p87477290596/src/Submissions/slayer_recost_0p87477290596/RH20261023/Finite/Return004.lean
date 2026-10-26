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
def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(821201266638052188798880827738455617/5555094342957980119750781250000:ℝ),(2355775452976176420924969921946846531/5555094342957980119750781250000:ℝ),(2250165581932150355295058816673776163/5555094342957980119750781250000:ℝ),(715578192118903497578191072465385249/5555094342957980119750781250000:ℝ)],
  ![(671969791571059928049114722788106209/2777547171478990059875390625000:ℝ),(1913198438221531198344992555963552899/2777547171478990059875390625000:ℝ),(1812905104813820292092252677695422891/2777547171478990059875390625000:ℝ),(571659953819445739807901532019976201/2777547171478990059875390625000:ℝ)],
  ![(107735512416021933032858276785911077/1111018868591596023950156250000:ℝ),(303798944636806647710386920036843671/1111018868591596023950156250000:ℝ),(284906879850655686146454421783693861/1111018868591596023950156250000:ℝ),(88839321543895150971807450407761267/1111018868591596023950156250000:ℝ)]
]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (88839321543895150971807450407761267/517772320512133952182026240000000000:ℝ) row004_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row004_coefficients,Fin.sum_univ_succ] <;> ring
theorem row004_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row004_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_coefficients]
#print axioms row004_identity
#print axioms row004_pos
end
end RH20261023Finite
