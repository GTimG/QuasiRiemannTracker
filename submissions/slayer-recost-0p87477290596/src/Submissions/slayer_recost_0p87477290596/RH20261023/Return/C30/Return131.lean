/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row131_coefficients : Fin 3 → Fin 4 → ℝ := ![![(367941442121773125856274779/104935005165776639062500:ℝ), (903423962338097980878538537/104935005165776639062500:ℝ), (721818169225780145573258987/104935005165776639062500:ℝ), (185981428337442116019745229/104935005165776639062500:ℝ)],
![(2027152616195625114560907887/262337512914441597656250:ℝ), (4896918906316896183109764797/262337512914441597656250:ℝ), (3822953215921627379496441433/262337512914441597656250:ℝ), (951061601768277263760084523/262337512914441597656250:ℝ)],
![(2785041356527039046603381279/524675025828883195312500:ℝ), (6923870676079522115622187709/524675025828883195312500:ℝ), (5622672176489926306165311781/524675025828883195312500:ℝ), (1481292468098948380521505351/524675025828883195312500:ℝ)]]
theorem row131_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (185981428337442116019745229/48903256878537513369600000000:ℝ) row131_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row131_coefficients,Fin.sum_univ_succ]
 ring
theorem row131_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row131_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row131_coefficients]
#print axioms row131_identity
#print axioms row131_pos
end
end RH20261023Return.C30
