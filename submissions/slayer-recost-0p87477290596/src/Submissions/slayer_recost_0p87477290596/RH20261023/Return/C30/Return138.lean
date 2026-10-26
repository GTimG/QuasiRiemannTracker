/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row138_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29689207822087379176696709933/131168756457220798828125:ℝ), (76217985049825426090664395337/131168756457220798828125:ℝ), (2564707063567726438996767424/5246750258288831953125:ℝ), (17581088795637223562537437696/131168756457220798828125:ℝ)],
![(60496821760079785109995642252/131168756457220798828125:ℝ), (30919629900724703942501190764/26233751291444159765625:ℝ), (129267081701853394251620662784/131168756457220798828125:ℝ), (35149388963262650985766601216/131168756457220798828125:ℝ)],
![(31768456023598199366543003444/131168756457220798828125:ℝ), (81206678917821801372673638308/131168756457220798828125:ℝ), (67921189006956410703962781184/131168756457220798828125:ℝ), (3694878794494017974835179264/26233751291444159765625:ℝ)]]
theorem row138_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (68651150318872365206575393/30564535549085945856000000000:ℝ) row138_coefficients (63/128:ℝ) (33/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row138_coefficients,Fin.sum_univ_succ]
 ring
theorem row138_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row138_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row138_coefficients]
#print axioms row138_identity
#print axioms row138_pos
end
end RH20261023Return.C30
