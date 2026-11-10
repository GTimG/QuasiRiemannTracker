import Candidate.Local.Qrh.PositiveGap.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.PositiveGap.Return
noncomputable section
variable [TargetC]
theorem countJ_pos (b : CountBranch) {δ p : ℝ}
 (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) : 0<countJ b δ p := by
 have hv : 0<V δ := by dsimp [V]; linarith [hδ.2]
 have hdp : 0≤δ*(1-p) := mul_nonneg hδ.1 (by linarith [hp.2])
 have hk3 : (2 : ℝ) < 3 * kappa := by unfold kappa; linarith [c_hi]
 have hp2k : 2 * p / (3 * kappa) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [hp.2])
 have hpk : p / (3 * kappa) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [hp.2])
 have hd : 0<oldD p := by unfold oldD; linarith [hp.2, hp2k]
 have hc : 0≤oldC p := by
  unfold oldC
  exact mul_nonneg (by linarith [hp.2]) (by linarith [hpk])
 have hLC : 2 < countCL := by unfold countCL; linarith [eps_pos]
 have hLP : 2 < physicalLambda := by unfold physicalLambda; linarith [eps_pos]
 have hpLC : 4 * p / countCL ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [hp.2])
 have hpLP : 4 * p / physicalLambda ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [hp.2])
 have had (b : CountBranch) : 0<D b p := by
  cases b <;> dsimp [D, isCap, branchL] <;> linarith [hp.2, hpLC, hpLP]
 have haa (b : CountBranch) : 0≤A b p := by
  cases b <;> dsimp [A, isCap, branchL] <;> linarith [hp.2, hpLC, hpLP]
 cases b with
 | old => exact add_pos_of_pos_of_nonneg (mul_pos hv hd) (mul_nonneg hδ.1 hc)
 | C => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .C)) (mul_nonneg hdp (haa .C))
 | capC => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capC)) (mul_nonneg hdp (haa .capC))
 | weakC7 => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .weakC7)) (mul_nonneg hdp (haa .weakC7))
 | capP => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capP)) (mul_nonneg hdp (haa .capP))
theorem edgeD_nonneg (e : Edge) : 0≤edgeD e := by
 cases e <;> dsimp [edgeD, dm, dp, d0, h] <;> linarith [c_lo, eps_pos]
theorem exponent_lt_of_margin {e : Edge} {b : CountBranch} {δ p R : ℝ}
 (hJ : 0<countJ b δ p) (hF : 0<rowMargin e b δ p)
 (hR : R≤countN b δ p/countJ b δ p) :
 Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R < theta-reserve := by
 have hd : 0≤3/4*edgeD e := by positivity [edgeD_nonneg e]
 have hRN := mul_le_mul_of_nonneg_left ((le_div_iff₀ hJ).mp hR) hd
 have hlt : countJ b δ p*(Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*R) <
  countJ b δ p*(theta-reserve) := by
  dsimp [rowMargin] at hF
  nlinarith only [hF,hRN]
 exact (mul_lt_mul_iff_right₀ hJ).mp hlt
end
end QRH.PositiveGap.Return
