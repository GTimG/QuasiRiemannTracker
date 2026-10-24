/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace RH20261023Return.C30
noncomputable section
def row110_coefficients : Fin 3 → Fin 4 → ℝ := ![![(57067562576969708266/3888805623046875:ℝ), (461343996259106649458/11666416869140625:ℝ), (414164843130822228622/11666416869140625:ℝ), (124023534602624703962/11666416869140625:ℝ)],
![(19588589180572532809/777761124609375:ℝ), (765388417910533692751/11666416869140625:ℝ), (660400084638237048572/11666416869140625:ℝ), (188840504436291347956/11666416869140625:ℝ)],
![(726539858465212042639/62220889968750000:ℝ), (5498248473428439100013/186662669906250000:ℝ), (11386611077711787922/466656674765625:ℝ), (77250970815744512294/11666416869140625:ℝ)]]
theorem row110_identity (δ p : ℝ) : rowMargin .newSwitch .capC δ p =
 Record12518109.Bernstein.bsum 2 3 (38625485407872256147/10873888653312000000000:ℝ) row110_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row110_coefficients,Fin.sum_univ_succ]
 ring
theorem row110_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capC δ p := by
 rw [row110_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row110_coefficients]
#print axioms row110_identity
#print axioms row110_pos
end
end RH20261023Return.C30
