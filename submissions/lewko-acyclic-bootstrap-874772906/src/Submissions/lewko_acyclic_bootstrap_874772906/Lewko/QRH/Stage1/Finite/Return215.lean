/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def row215_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44507772180797542907737785148181569/20695701249213535491852459375000:ℝ),(98680130482896414449288838421522507/20695701249213535491852459375000:ℝ),(67457731173589230400714833359609057/20695701249213535491852459375000:ℝ),(13215613290198434794829695398768119/20695701249213535491852459375000:ℝ)],
![(296731935949779056315879036570096957/51739253123033838729631148437500:ℝ),(677863376229512992816929135199233767/51739253123033838729631148437500:ℝ),(486914188763086208339040505419274363/51739253123033838729631148437500:ℝ),(105364190995600727451985898665137553/51739253123033838729631148437500:ℝ)],
![(480683787392223309437749088695263629/103478506246067677459262296875000:ℝ),(1178602565019580759661484107612782919/103478506246067677459262296875000:ℝ),(940403889229284313353963690374426431/103478506246067677459262296875000:ℝ),(241982842616625009867023261706907141/103478506246067677459262296875000:ℝ)]]
theorem row215_identity (δ p : ℝ) : rowMargin .newKink .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13215613290198434794829695398768119/9644895836931258751957637529600000000:ℝ) row215_coefficients (15/32:ℝ) (9/16:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newKink,edgeC_newKink,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row215_coefficients,Fin.sum_univ_succ]
 ring
theorem row215_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newKink .old δ p := by
 rw [row215_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row215_coefficients]
#print axioms row215_identity
#print axioms row215_pos
end
end LewkoStage1Finite
