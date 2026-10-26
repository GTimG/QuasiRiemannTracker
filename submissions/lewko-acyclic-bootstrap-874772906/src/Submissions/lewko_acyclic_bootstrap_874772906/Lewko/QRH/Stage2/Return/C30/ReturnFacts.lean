/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Return.C30
noncomputable section

theorem countJ_pos (b : CountBranch) {δ p : ℝ}
 (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0<countJ b δ p := by
 have hv : 0<V δ := by dsimp [V]; linarith [hδ.2]
 have hdp : 0≤δ*(1-p) := mul_nonneg hδ.1 (by linarith [hp.2])
 have hd : 0<oldD p := by norm_num [oldD,kappa,c]; nlinarith [hp.2]
 have hc : 0≤oldC p := by
  unfold oldC
  apply mul_nonneg
  · nlinarith [hp.2]
  · norm_num [kappa,c]; nlinarith [hp.2]
 have had (b : CountBranch) : 0<D b p := by
  cases b <;> norm_num [D,isCap,branchL,countCL,physicalLambda] <;> nlinarith [hp.2]
 have haa (b : CountBranch) : 0≤A b p := by
  cases b <;> norm_num [A,isCap,branchL,countCL,physicalLambda] <;> nlinarith [hp.2]
 cases b with
 | old => exact add_pos_of_pos_of_nonneg (mul_pos hv hd) (mul_nonneg hδ.1 hc)
 | C => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .C)) (mul_nonneg hdp (haa .C))
 | P => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .P)) (mul_nonneg hdp (haa .P))
 | capC => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capC)) (mul_nonneg hdp (haa .capC))
 | capP => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capP)) (mul_nonneg hdp (haa .capP))
 | weakC2 => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .weakC2)) (mul_nonneg hdp (haa .weakC2))
 | weakC6 => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .weakC6)) (mul_nonneg hdp (haa .weakC6))
 | weakC8 => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .weakC8)) (mul_nonneg hdp (haa .weakC8))


theorem edgeD_nonneg (e : Edge) : 0≤edgeD e := by
 cases e <;> norm_num [edgeD,ds,dk,dp,d0,y,h,ell,c,kappa,physicalB,physicalLambda]

/-- Requires the actual admitted count at the same witness. -/
theorem exponent_lt_of_margin {e : Edge} {b : CountBranch} {δ p R : ℝ}
 (hJ : 0<countJ b δ p) (hF : 0<rowMargin e b δ p)
 (hR : R≤countN b δ p/countJ b δ p) :
 Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R < theta-rowFee := by
 have hd : 0≤3/4*edgeD e := by positivity [edgeD_nonneg e]
 have hRN := mul_le_mul_of_nonneg_left ((le_div_iff₀ hJ).mp hR) hd
 have hlt : countJ b δ p*(Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R) <
  countJ b δ p*(theta-rowFee) := by
  dsimp [rowMargin] at hF
  nlinarith only [hF,hRN]
 exact (mul_lt_mul_iff_right₀ hJ).mp hlt
#print axioms countJ_pos
#print axioms edgeD_nonneg
#print axioms exponent_lt_of_margin
end
end LewkoStage2Return.C30
