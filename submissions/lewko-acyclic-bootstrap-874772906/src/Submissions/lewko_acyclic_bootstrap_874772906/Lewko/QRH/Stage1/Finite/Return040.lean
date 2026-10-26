/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row040_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3840568434645142698234569/14822561381835937500:ℝ),(278808637492392538633366343/370564034545898437500:ℝ),(89900700038528664518351059/123521344848632812500:ℝ),(28969224496440674125850353/123521344848632812500:ℝ)],
![(346355633287233194864905561/741128069091796875000:ℝ),(334018256061317851528073083/247042689697265625000:ℝ),(241399559016556991873842633/185282017272949218750:ℝ),(77474775292376901944014211/185282017272949218750:ℝ)],
![(830832843621205818988198609/3952683035156250000000:ℝ),(1436167593658933061297000023/2371609821093750000000:ℝ),(215281846813962129971918951/370564034545898437500:ℝ),(68771239394241884674406317/370564034545898437500:ℝ)]]
theorem row040_identity (δ p : ℝ) : rowMargin .oldPeak .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (68771239394241884674406317/690781427712000000000000000:ℝ) row040_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row040_coefficients,Fin.sum_univ_succ]
 ring
theorem row040_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .capC δ p := by
 rw [row040_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_coefficients]
#print axioms row040_identity
#print axioms row040_pos
end
end LewkoStage1Finite
