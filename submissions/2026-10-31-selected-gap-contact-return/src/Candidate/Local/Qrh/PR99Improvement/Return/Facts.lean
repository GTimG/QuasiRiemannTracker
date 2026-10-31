/- Adapted by Joseph Bebel (2026-10-30, 2026-10-31) for the fixed five-window return. -/
/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/
/- Modified by Sil (2026-10-26): three branches; the margin uses the certificate `reserve`. -/
/- Modified by ArviFoxy (2026-10-28): the branches `capC` (capped count face) and `weakC7` (count face with B - 7/4000) of PR 76's FinalReturn restored; module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Candidate.Local.Qrh.PR99Improvement.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.PR99Improvement.Return
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
 | capC => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capC)) (mul_nonneg hdp (haa .capC))
 | weakC7 => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .weakC7)) (mul_nonneg hdp (haa .weakC7))
 | capP => exact add_pos_of_pos_of_nonneg (mul_pos hv (had .capP)) (mul_nonneg hdp (haa .capP))

theorem edgeD_nonneg (e : Edge) : 0≤edgeD e := by
 cases e <;> norm_num [edgeD,dm,dp,d0,h]

/-- Requires the actual admitted count at the same witness. -/
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
end QRH.PR99Improvement.Return
