/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row140_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1863989838975071352684341/38864816728065421875000:ℝ), (89043250856620461985797967/1049350051657766390625000:ℝ), (22636489062065594357149669/524675025828883195312500:ℝ), (2641129250295112469239289/524675025828883195312500:ℝ)],
![(658799069899312914250114/4858102091008177734375:ℝ), (65451055115453501819239889/262337512914441597656250:ℝ), (3601549145062679798458441/26233751291444159765625:ℝ), (5289456496904574659850677/262337512914441597656250:ℝ)],
![(704865292290381432199991/6477469454677570312500:ℝ), (114918913306587432717118157/524675025828883195312500:ℝ), (73974972375371657457402301/524675025828883195312500:ℝ), (3003328318772592449696683/104935005165776639062500:ℝ)]]
theorem row140_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2641129250295112469239289/955141735908935808000000000:ℝ) row140_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row140_coefficients,Fin.sum_univ_succ]
 ring
theorem row140_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row140_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row140_coefficients]
#print axioms row140_identity
#print axioms row140_pos
end
end RH20261023Return.C30
