/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row107_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29573801046501558232516283/2098700103315532781250000:ℝ), (63918852737182680809833301/2098700103315532781250000:ℝ), (44369828298559928646659203/2098700103315532781250000:ℝ), (1948280014053653288868437/419740020663106556250000:ℝ)],
![(43359108131723702982586067/1049350051657766390625000:ℝ), (85675130876897760203715899/1049350051657766390625000:ℝ), (51231445882345142071155997/1049350051657766390625000:ℝ), (1669734012390001120005233/209870010331553278125000:ℝ)],
![(124302818523042896732655851/2098700103315532781250000:ℝ), (282305760820307999294960297/2098700103315532781250000:ℝ), (210522996311573263939716841/2098700103315532781250000:ℝ), (10277309572773200575482479/419740020663106556250000:ℝ)]]
theorem row107_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1669734012390001120005233/191028347181787161600000000:ℝ) row107_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row107_coefficients,Fin.sum_univ_succ]
 ring
theorem row107_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row107_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row107_coefficients]
#print axioms row107_identity
#print axioms row107_pos
end
end RH20261023Return.C30
